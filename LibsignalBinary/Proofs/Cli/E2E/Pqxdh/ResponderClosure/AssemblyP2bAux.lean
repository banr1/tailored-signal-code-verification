/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP2a
public import LibsignalBinary.Proofs.TripleRatchet.TrapRng
public import ProofLib.SepLogic.WP
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.StageP1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.StageP2a
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Responder Closure Stage P2.4–P2.6 Segment & Framing Helpers

Frame-pointer-generalized Stage P2.5b/P2.5c1 `SepWP` lemmas, `SessionState` framing helpers,
and Stage P2.4 / P2.6e / Err3b segment lemmas for `message_decrypt_prekey::<Coins>::{closure#0}`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession

open CryptoVerification.RustHeap

open CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.E2E.InMem

set_option maxRecDepth 200000

set_option maxHeartbeats 1600000

set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")

/-! ## 1. Frame-Pointer-Generalized Stage P2.5b & P2.5c1 Segments -/

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg5b_fp_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr msgPtr ctxPtr idKpFutPtr idKpFutVt idKpDropAddr fp
    v_98 v_a0 v_b0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 u_fp80 : BitVec 64)
    (opkId : BitVec 32)
    (b0 b1 b2 b3 b4 b5 b6 b63
     s0 s1_b s2 s3 s4 s5 s6 b_fp78 : BitVec 8)
    (w0 w1 w2 w3 w4 w5 w6 : BitVec 64)
    (hdrop_nz : idKpDropAddr ≠ 0#64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x7bc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = v_a0)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx26 : s.readReg64 .x26 = v_98)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx29 : s.readReg64 .x29 = fp) :
    SepWP (trTrapProgAt b C abs) idKpDropAddr s
      (((s.sp + 0x3e0#64) ↦₈ 0#8) ∗
       keyPair64UnalignedAt (s.sp + 0x3e1#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
       bytes7At (s.sp + 0x3c8#64) s0 s1_b s2 s3 s4 s5 s6 ∗
       ((fp + 0xffffffffffffff80#64) ↦₆₄ u_fp80) ∗
       ((fp + 0xffffffffffffff88#64) ↦₈ b_fp78) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ idKpFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ idKpFutVt) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((idKpFutVt + 0x0#64) ↦₆₄ᵣ idKpDropAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e0#64) ↦₈ 0#8) ∗
          keyPair64UnalignedAt (s.sp + 0x3e1#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
          bytes7At (s.sp + 0x3c8#64) b0 b1 b2 b3 b4 b5 b6 ∗
          ((fp + 0xffffffffffffff80#64) ↦₆₄ w6) ∗
          ((fp + 0xffffffffffffff88#64) ↦₈ b63) ∗
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xa8#64) ↦₆₄ w4) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ w2) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((s.sp + 0xd0#64) ↦₆₄ w3) ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ idKpFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ idKpFutVt) ∗
          ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
          ((idKpFutVt + 0x0#64) ↦₆₄ᵣ idKpDropAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = idKpFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = w0 ∧
        s1.readReg64 .x21 = idKpFutPtr ∧
        s1.readReg64 .x22 = 0#64 ∧
        s1.readReg64 .x23 = w1 ∧
        s1.readReg64 .x24 = idKpFutVt ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_98 ∧
        s1.readReg64 .x27 = w5 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = fp ∧
        s1.readReg64 .x30 = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
          0xac4#64) := by
  have hdrop_beq : (idKpDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x7bc 0x7c4
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xa60 0xac0
  dsimp only [trTrapProgAt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = v_b0 := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = v_a0 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx26' : s.readReg64 (Reg.gpr 26#5) = v_98 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = ctxPtr := hx27
  have hx29' : s.readReg64 (Reg.gpr 29#5) = fp := hx29
  dsimp only [keyPair64UnalignedAt, bytes7At]
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

/-- Segment P2.5b (`+0x07bc -> idKpDropAddr`, generalized over `fp = s.readReg64 .x29`): Unpacks the 64-byte `IdentityKeyPair` from `sp + 0x3e1..0x420` into `sp + 0x3c8..0x3ce`,
`fp - 0x80` (`w6`), `fp - 0x78` (`b63`), `sp + 0xa8..0xd0` and registers `x20, x23, x27`,
loads `idKpDropAddr` from `[idKpFutVt + 0x0]`, sets `x0 = idKpFutPtr`,
  and calls `blr x8` at `+0x0ac0`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg5b_fp_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr msgPtr ctxPtr idKpFutPtr idKpFutVt idKpDropAddr fp
    v_98 v_a0 v_b0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 u_fp80 : BitVec 64)
    (opkId : BitVec 32)
    (b0 b1 b2 b3 b4 b5 b6 b63
     s0 s1_b s2 s3 s4 s5 s6 b_fp78 : BitVec 8)
    (w0 w1 w2 w3 w4 w5 w6 : BitVec 64)
    (hdrop_nz : idKpDropAddr ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x7bc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = v_a0)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx26 : s.readReg64 .x26 = v_98)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx29 : s.readReg64 .x29 = fp) :
    SepWP (tripleRatchetProgAt b C ctl abs) idKpDropAddr s
      (((s.sp + 0x3e0#64) ↦₈ 0#8) ∗
       keyPair64UnalignedAt (s.sp + 0x3e1#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
       bytes7At (s.sp + 0x3c8#64) s0 s1_b s2 s3 s4 s5 s6 ∗
       ((fp + 0xffffffffffffff80#64) ↦₆₄ u_fp80) ∗
       ((fp + 0xffffffffffffff88#64) ↦₈ b_fp78) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ idKpFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ idKpFutVt) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((idKpFutVt + 0x0#64) ↦₆₄ᵣ idKpDropAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e0#64) ↦₈ 0#8) ∗
          keyPair64UnalignedAt (s.sp + 0x3e1#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
          bytes7At (s.sp + 0x3c8#64) b0 b1 b2 b3 b4 b5 b6 ∗
          ((fp + 0xffffffffffffff80#64) ↦₆₄ w6) ∗
          ((fp + 0xffffffffffffff88#64) ↦₈ b63) ∗
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xa8#64) ↦₆₄ w4) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ w2) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((s.sp + 0xd0#64) ↦₆₄ w3) ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ idKpFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ idKpFutVt) ∗
          ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
          ((idKpFutVt + 0x0#64) ↦₆₄ᵣ idKpDropAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = idKpFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = w0 ∧
        s1.readReg64 .x21 = idKpFutPtr ∧
        s1.readReg64 .x22 = 0#64 ∧
        s1.readReg64 .x23 = w1 ∧
        s1.readReg64 .x24 = idKpFutVt ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_98 ∧
        s1.readReg64 .x27 = w5 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = fp ∧
        s1.readReg64 .x30 = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
          0xac4#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg5b_fp_wp_trap b C abs s
      coroPtr msgPtr ctxPtr idKpFutPtr idKpFutVt idKpDropAddr fp
      v_98 v_a0 v_b0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 u_fp80 opkId
      b0 b1 b2 b3 b4 b5 b6 b63 s0 s1_b s2 s3 s4 s5 s6 b_fp78
      w0 w1 w2 w3 w4 w5 w6 hdrop_nz hpc hrun hsp_align
      hx19 hx21 hx23 hx24 hx26 hx27 hx29)

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg5c1_fp_wp_trap {A : RustAlloc} (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr msgPtr remoteAddrPtr localAddrPtr idKpFutPtr idKpFutVt fp
    kyberPreKeyId64 w0 w1 w2 w3 w4 w5 w6
    cw0 cw1 cw2 cw3 cw4 cw5 : BitVec 64)
    (opkId : BitVec 32)
    (b0 b1 b2 b3 b4 b5 b6 b63
     c0 c1 c2 c3 c4 c5 c6 : BitVec 8)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xac4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = idKpFutPtr)
    (hx22 : s.readReg64 .x22 = 0#64)
    (hx23 : s.readReg64 .x23 = w1)
    (hx24 : s.readReg64 .x24 = idKpFutVt)
    (hx27 : s.readReg64 .x27 = w5)
    (hx29 : s.readReg64 .x29 = fp) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x114c#64) s
      (((idKpFutVt + 0x8#64) ↦₆₄ᵣ 16#64) ∗
       ((idKpFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live idKpFutPtr 16 8 ∗
       memRegion idKpFutPtr 16 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       bytes7At (s.sp + 0x3c8#64) b0 b1 b2 b3 b4 b5 b6 ∗
       bytes7At (coroPtr + 0x798#64) c0 c1 c2 c3 c4 c5 c6 ∗
       ((coroPtr + 0x79f#64) ↦₆₄ cw0) ∗
       ((coroPtr + 0x7a7#64) ↦₆₄ cw1) ∗
       ((coroPtr + 0x7af#64) ↦₆₄ cw2) ∗
       ((coroPtr + 0x7b7#64) ↦₆₄ cw3) ∗
       ((coroPtr + 0x7bf#64) ↦₆₄ cw4) ∗
       ((coroPtr + 0x7c7#64) ↦₆₄ cw5) ∗
       ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((s.sp + 0xa8#64) ↦₆₄ w4) ∗
       ((s.sp + 0xb8#64) ↦₆₄ w2) ∗
       ((s.sp + 0xd0#64) ↦₆₄ w3) ∗
       ((fp + 0xffffffffffffff80#64) ↦₆₄ w6) ∗
       ((fp + 0xffffffffffffff88#64) ↦₈ b63) ∗
       ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
       ((coroPtr + 0x488#64) ↦₆₄ kyberPreKeyId64) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId))
      (fun s1 P_f =>
        (P_f ⊢
          ((idKpFutVt + 0x8#64) ↦₆₄ᵣ 16#64) ∗
          ((idKpFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          bytes7At (s.sp + 0x3c8#64) b0 b1 b2 b3 b4 b5 b6 ∗
          bytes7At (coroPtr + 0x798#64) b0 b1 b2 b3 b4 b5 b6 ∗
          ((coroPtr + 0x79f#64) ↦₆₄ w0) ∗
          ((coroPtr + 0x7a7#64) ↦₆₄ w1) ∗
          ((coroPtr + 0x7af#64) ↦₆₄ w2) ∗
          ((coroPtr + 0x7b7#64) ↦₆₄ w3) ∗
          ((coroPtr + 0x7bf#64) ↦₆₄ w4) ∗
          ((coroPtr + 0x7c7#64) ↦₆₄ w5) ∗
          ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((s.sp + 0xa8#64) ↦₆₄ w4) ∗
          ((s.sp + 0xb8#64) ↦₆₄ w2) ∗
          ((s.sp + 0xd0#64) ↦₆₄ w3) ∗
          ((fp + 0xffffffffffffff80#64) ↦₆₄ w6) ∗
          ((fp + 0xffffffffffffff88#64) ↦₈ b63) ∗
          ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
          ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
          ((coroPtr + 0x488#64) ↦₆₄ kyberPreKeyId64) ∗
          ((msgPtr + 0x7c#64) ↦₃₂ opkId)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0x798#64 ∧
        s1.readReg64 .x1 = localAddrPtr ∧
        s1.readReg64 .x3 = remoteAddrPtr ∧
        s1.readReg64 .x8 = b63.zeroExtend 64 ∧
        s1.readReg64 .x9 = w6 ∧
        s1.readReg64 .x10 = coroPtr + 0x798#64 ∧
        s1.readReg64 .x11 = coroPtr + 0x7cf#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = kyberPreKeyId64 ∧
        s1.readReg64 .x22 = s.sp + 0x370#64 ∧
        s1.readReg64 .x23 = s.sp + 0x930#64 ∧
        s1.readReg64 .x24 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = w5 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = fp) := by
  have hdealloc := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_dealloc_ok_trap (b := b) (C := C)
    (abs := abs) hA
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xac4 0xad8
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x10e8 0x1148
  dsimp only [trTrapProgAt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = w0 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = idKpFutPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = 0#64 := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = w1 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = idKpFutVt := hx24
  have hx27' : s.readReg64 (Reg.gpr 27#5) = w5 := hx27
  have hx29' : s.readReg64 (Reg.gpr 29#5) = fp := hx29
  dsimp only [bytes7At]
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  wp_call hdealloc (idKpFutPtr, 16, 8)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
  have hfp80 : fp - 128#64 = fp + 0xffffffffffffff80#64 := by bv_omega
  have hfp78 : fp - 120#64 = fp + 0xffffffffffffff88#64 := by bv_omega
  simp only [hfp80, hfp78, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

/-- Segment P2.5c1 (`+0x0ac4 -> +0x114c`, generalized over `fp = s.readReg64 .x29`): Deallocates `idKpFutPtr` (`__rust_dealloc`), branches (`tbz w22, #0`) to `+0x10e8`, writes the
first 55 bytes (`b0..b6` and `w0..w5`) of `IdentityKeyPair` into `coroPtr + 0x798..0x7ce`,
loads `w8 = b63` and `x9 = w6` from `fp - 0x78` and `fp - 0x80`, and stops at `+0x114c`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg5c1_fp_wp {A : RustAlloc} (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr msgPtr remoteAddrPtr localAddrPtr idKpFutPtr idKpFutVt fp
    kyberPreKeyId64 w0 w1 w2 w3 w4 w5 w6
    cw0 cw1 cw2 cw3 cw4 cw5 : BitVec 64)
    (opkId : BitVec 32)
    (b0 b1 b2 b3 b4 b5 b6 b63
     c0 c1 c2 c3 c4 c5 c6 : BitVec 8)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xac4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = idKpFutPtr)
    (hx22 : s.readReg64 .x22 = 0#64)
    (hx23 : s.readReg64 .x23 = w1)
    (hx24 : s.readReg64 .x24 = idKpFutVt)
    (hx27 : s.readReg64 .x27 = w5)
    (hx29 : s.readReg64 .x29 = fp) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x114c#64) s
      (((idKpFutVt + 0x8#64) ↦₆₄ᵣ 16#64) ∗
       ((idKpFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live idKpFutPtr 16 8 ∗
       memRegion idKpFutPtr 16 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       bytes7At (s.sp + 0x3c8#64) b0 b1 b2 b3 b4 b5 b6 ∗
       bytes7At (coroPtr + 0x798#64) c0 c1 c2 c3 c4 c5 c6 ∗
       ((coroPtr + 0x79f#64) ↦₆₄ cw0) ∗
       ((coroPtr + 0x7a7#64) ↦₆₄ cw1) ∗
       ((coroPtr + 0x7af#64) ↦₆₄ cw2) ∗
       ((coroPtr + 0x7b7#64) ↦₆₄ cw3) ∗
       ((coroPtr + 0x7bf#64) ↦₆₄ cw4) ∗
       ((coroPtr + 0x7c7#64) ↦₆₄ cw5) ∗
       ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((s.sp + 0xa8#64) ↦₆₄ w4) ∗
       ((s.sp + 0xb8#64) ↦₆₄ w2) ∗
       ((s.sp + 0xd0#64) ↦₆₄ w3) ∗
       ((fp + 0xffffffffffffff80#64) ↦₆₄ w6) ∗
       ((fp + 0xffffffffffffff88#64) ↦₈ b63) ∗
       ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
       ((coroPtr + 0x488#64) ↦₆₄ kyberPreKeyId64) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId))
      (fun s1 P_f =>
        (P_f ⊢
          ((idKpFutVt + 0x8#64) ↦₆₄ᵣ 16#64) ∗
          ((idKpFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          bytes7At (s.sp + 0x3c8#64) b0 b1 b2 b3 b4 b5 b6 ∗
          bytes7At (coroPtr + 0x798#64) b0 b1 b2 b3 b4 b5 b6 ∗
          ((coroPtr + 0x79f#64) ↦₆₄ w0) ∗
          ((coroPtr + 0x7a7#64) ↦₆₄ w1) ∗
          ((coroPtr + 0x7af#64) ↦₆₄ w2) ∗
          ((coroPtr + 0x7b7#64) ↦₆₄ w3) ∗
          ((coroPtr + 0x7bf#64) ↦₆₄ w4) ∗
          ((coroPtr + 0x7c7#64) ↦₆₄ w5) ∗
          ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((s.sp + 0xa8#64) ↦₆₄ w4) ∗
          ((s.sp + 0xb8#64) ↦₆₄ w2) ∗
          ((s.sp + 0xd0#64) ↦₆₄ w3) ∗
          ((fp + 0xffffffffffffff80#64) ↦₆₄ w6) ∗
          ((fp + 0xffffffffffffff88#64) ↦₈ b63) ∗
          ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
          ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
          ((coroPtr + 0x488#64) ↦₆₄ kyberPreKeyId64) ∗
          ((msgPtr + 0x7c#64) ↦₃₂ opkId)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0x798#64 ∧
        s1.readReg64 .x1 = localAddrPtr ∧
        s1.readReg64 .x3 = remoteAddrPtr ∧
        s1.readReg64 .x8 = b63.zeroExtend 64 ∧
        s1.readReg64 .x9 = w6 ∧
        s1.readReg64 .x10 = coroPtr + 0x798#64 ∧
        s1.readReg64 .x11 = coroPtr + 0x7cf#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = kyberPreKeyId64 ∧
        s1.readReg64 .x22 = s.sp + 0x370#64 ∧
        s1.readReg64 .x23 = s.sp + 0x930#64 ∧
        s1.readReg64 .x24 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = w5 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = fp) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg5c1_fp_wp_trap b C abs hA s
      coroPtr msgPtr remoteAddrPtr localAddrPtr idKpFutPtr idKpFutVt fp
      kyberPreKeyId64 w0 w1 w2 w3 w4 w5 w6 cw0 cw1 cw2 cw3 cw4 cw5 opkId
      b0 b1 b2 b3 b4 b5 b6 b63 c0 c1 c2 c3 c4 c5 c6
      hpc hrun hsp_align hx19 hx20 hx21 hx22 hx23 hx24 hx27 hx29)

/-! ## 2. `SessionState` & Stage P2.4–P2.6 Framing Helpers -/

open CryptoVerification.E2E.InMem

open CryptoVerification.E2E.InMem.HashbrownModel

open CryptoVerification.E2E.InMem.HashbrownBin

open CryptoVerification.LibsignalTripleRatchet.Getters

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_err4_1568_wp_trap {A : RustAlloc} (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr kyberKpPubPtr kyberKpSecPtr errTag outPtr
    w2 w3 w4 w5 w6 u_88 u_a8 u_b8 u_d0 : BitVec 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x125c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx28 : s.readReg64 .x28 = s.sp + 0xa90#64) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1648#64) s
      (((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ errTag) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ w2) ∗
       ((s.sp + 0x3f8#64) ↦₆₄ w3) ∗
       ((s.sp + 0x400#64) ↦₆₄ w4) ∗
       ((s.sp + 0x408#64) ↦₆₄ w5) ∗
       ((s.sp + 0x410#64) ↦₆₄ w6) ∗
       ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗
       ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x728#64) ↦₆₄ kyberKpSecPtr) ∗
       ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
       A.live kyberKpPubPtr 1568 1 ∗
       memRegion kyberKpPubPtr 1568 ∗
       A.live kyberKpSecPtr 3168 1 ∗
       memRegion kyberKpSecPtr 3168 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
       ((s.sp + 0x88#64) ↦₆₄ u_88) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          ((s.sp + 0x3e8#64) ↦₆₄ errTag) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ w2) ∗
          ((s.sp + 0x3f8#64) ↦₆₄ w3) ∗
          ((s.sp + 0x400#64) ↦₆₄ w4) ∗
          ((s.sp + 0x408#64) ↦₆₄ w5) ∗
          ((s.sp + 0x410#64) ↦₆₄ w6) ∗
          ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗
          ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
          ((coroPtr + 0x728#64) ↦₆₄ kyberKpSecPtr) ∗
          ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
          ((s.sp + 0x88#64) ↦₆₄ errTag) ∗
          ((s.sp + 0xa8#64) ↦₆₄ w5) ∗
          ((s.sp + 0xb8#64) ↦₆₄ w3) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((s.sp + 0xd0#64) ↦₆₄ w4)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = errTag ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x27 = w6 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  have hdealloc := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_dealloc_ok_trap (b := b) (C := C)
    (abs := abs) hA
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x125c 0x127c
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x15b8 0x1608
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x163c 0x1644
  dsimp only [trTrapProgAt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx28' : s.readReg64 (Reg.gpr 28#5) = s.sp + 0xa90#64 := hx28
  wp_steps
  wp_call hdealloc (kyberKpPubPtr, 1568, 1)
  wp_steps
  wp_call hdealloc (kyberKpSecPtr, 3168, 1)
  wp_steps
  rw [hsp_sf]
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_err4_1568_wp {A : RustAlloc} (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr kyberKpPubPtr kyberKpSecPtr errTag outPtr
    w2 w3 w4 w5 w6 u_88 u_a8 u_b8 u_d0 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x125c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx28 : s.readReg64 .x28 = s.sp + 0xa90#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1648#64) s
      (((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ errTag) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ w2) ∗
       ((s.sp + 0x3f8#64) ↦₆₄ w3) ∗
       ((s.sp + 0x400#64) ↦₆₄ w4) ∗
       ((s.sp + 0x408#64) ↦₆₄ w5) ∗
       ((s.sp + 0x410#64) ↦₆₄ w6) ∗
       ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗
       ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x728#64) ↦₆₄ kyberKpSecPtr) ∗
       ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
       A.live kyberKpPubPtr 1568 1 ∗
       memRegion kyberKpPubPtr 1568 ∗
       A.live kyberKpSecPtr 3168 1 ∗
       memRegion kyberKpSecPtr 3168 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
       ((s.sp + 0x88#64) ↦₆₄ u_88) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          ((s.sp + 0x3e8#64) ↦₆₄ errTag) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ w2) ∗
          ((s.sp + 0x3f8#64) ↦₆₄ w3) ∗
          ((s.sp + 0x400#64) ↦₆₄ w4) ∗
          ((s.sp + 0x408#64) ↦₆₄ w5) ∗
          ((s.sp + 0x410#64) ↦₆₄ w6) ∗
          ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗
          ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
          ((coroPtr + 0x728#64) ↦₆₄ kyberKpSecPtr) ∗
          ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
          ((s.sp + 0x88#64) ↦₆₄ errTag) ∗
          ((s.sp + 0xa8#64) ↦₆₄ w5) ∗
          ((s.sp + 0xb8#64) ↦₆₄ w3) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((s.sp + 0xd0#64) ↦₆₄ w4)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = errTag ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x27 = w6 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_err4_1568_wp_trap b C abs hA s
      coroPtr kyberKpPubPtr kyberKpSecPtr errTag outPtr w2 w3 w4 w5 w6
      u_88 u_a8 u_b8 u_d0 hpc hrun hsp_align hx19 hx28)

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg6e_1568_wp_trap {A : RustAlloc} (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr msgPtr kyberCtCap kyberKpPubPtr kyberKpSecPtr
    v_c8 u_a8 u_d0 : BitVec 64)
    (opkIdIsSome opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_4f1 b_4f2 : BitVec 8)
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xb90#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>" - ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64)) s
      (((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗
       ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x728#64) ↦₆₄ kyberKpSecPtr) ∗
       ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((msgPtr + 0x78#64) ↦₃₂ opkIdIsSome) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
       ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
       ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗
       ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xc8#64) ↦₆₄ v_c8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       A.live kyberKpPubPtr 1568 1 ∗ memRegion kyberKpPubPtr 1568 ∗
       A.live kyberKpSecPtr 3168 1 ∗ memRegion kyberKpSecPtr 3168 ∗
       A.pool ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗
          ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
          ((coroPtr + 0x728#64) ↦₆₄ kyberKpSecPtr) ∗
          ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
          ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          ((msgPtr + 0x78#64) ↦₃₂ opkIdIsSome) ∗
          ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
          ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
          ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
          ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗
          ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
          ((s.sp + 0xa8#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0xc8#64) ↦₆₄ v_c8) ∗
          ((s.sp + 0xd0#64) ↦₆₄ signedPreKeyId.zeroExtend 64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x21 = 0#64 ∧
        s1.readReg64 .x22 = (kyberPreKeyId.zeroExtend 64 <<< 32) ||| 1#64 ∧
        s1.readReg64 .x23 = opkIdIsSome.zeroExtend 64 ∧
        s1.readReg64 .x24 = opkIdIsSome.zeroExtend 64 ||| (opkId.zeroExtend 64 <<< 32) ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_c8 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
          0x1698#64) := by
  have hdealloc := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_dealloc_ok_trap (b := b) (C := C)
    (abs := abs) hA
  have hkyber_beq : (kyberCtCap - 0#64 == 0#64) = false := by
    rw [BitVec.sub_zero]; exact beq_eq_false_iff_ne.mpr hkyber_nz
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xb90 0xbf0
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1648 0x1658
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1678 0x1694
  dsimp only [trTrapProgAt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  wp_call hdealloc (kyberKpPubPtr, 1568, 1)
  wp_steps
  wp_call hdealloc (kyberKpSecPtr, 3168, 1)
  wp_steps
  rw [hsp_sf]
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm]; clear * -; bv_slice,
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P2.6e (`+0x0b90 -> {closure#0}> [local#2]`, `1568`/`3168` Kyber KeyPair dealloc sizes): Reads `(opkIdIsSome, opkId)`, `kyberPreKeyId`, `signedPreKeyId` from `msgPtr`, deallocates
`kyberKpPubPtr` (`1568`) and `kyberKpSecPtr` (`3168`), sets `[coroPtr + 0x4f1] = 0#8` and
`[coroPtr + 0x4f2] = 1#8`, packs `x22` and `x24`, sets `x0 = coroPtr + 0x398`, and calls
`bl {closure#0}> [local#2]` (`drop_glue::<process_prekey_impl>`) at `+0x1694`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg6e_1568_wp {A : RustAlloc} (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr msgPtr kyberCtCap kyberKpPubPtr kyberKpSecPtr
    v_c8 u_a8 u_d0 : BitVec 64)
    (opkIdIsSome opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_4f1 b_4f2 : BitVec 8)
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xb90#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>" - ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64)) s
      (((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗
       ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x728#64) ↦₆₄ kyberKpSecPtr) ∗
       ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((msgPtr + 0x78#64) ↦₃₂ opkIdIsSome) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
       ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
       ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗
       ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xc8#64) ↦₆₄ v_c8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       A.live kyberKpPubPtr 1568 1 ∗ memRegion kyberKpPubPtr 1568 ∗
       A.live kyberKpSecPtr 3168 1 ∗ memRegion kyberKpSecPtr 3168 ∗
       A.pool ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗
          ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
          ((coroPtr + 0x728#64) ↦₆₄ kyberKpSecPtr) ∗
          ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
          ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          ((msgPtr + 0x78#64) ↦₃₂ opkIdIsSome) ∗
          ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
          ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
          ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
          ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗
          ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
          ((s.sp + 0xa8#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0xc8#64) ↦₆₄ v_c8) ∗
          ((s.sp + 0xd0#64) ↦₆₄ signedPreKeyId.zeroExtend 64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x21 = 0#64 ∧
        s1.readReg64 .x22 = (kyberPreKeyId.zeroExtend 64 <<< 32) ||| 1#64 ∧
        s1.readReg64 .x23 = opkIdIsSome.zeroExtend 64 ∧
        s1.readReg64 .x24 = opkIdIsSome.zeroExtend 64 ||| (opkId.zeroExtend 64 <<< 32) ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_c8 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
          0x1698#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg6e_1568_wp_trap b C abs hA s
      coroPtr msgPtr kyberCtCap kyberKpPubPtr kyberKpSecPtr v_c8 u_a8 u_d0
      opkIdIsSome opkId kyberPreKeyId signedPreKeyId b_4f1 b_4f2
      hkyber_nz hpc hrun hsp_align hx19)

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg4_none_64_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr msgPtr ctxPtr idStorePtr idStoreVt getIdKpShimAddr
    ctSlicePtr v_b0 u_488 : BitVec 64)
    (opkId : BitVec 32) (b_4b0 : BitVec 8)
    (hb : b &&& 0xfff#64 = 0#64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xd5c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = ctSlicePtr) :
    SepWP (trTrapProgAt b C abs) getIdKpShimAddr s
      (((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
       ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x488#64) ↦₆₄ u_488) ∗
       ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
       ((msgPtr + 0x78#64) ↦₃₂ 0#32) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((idStoreVt + 0x18#64) ↦₆₄ᵣ getIdKpShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
          ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((coroPtr + 0x488#64) ↦₆₄ ctSlicePtr) ∗
          ((coroPtr + 0x4b0#64) ↦₈ 0#8) ∗
          ((msgPtr + 0x78#64) ↦₃₂ 0#32) ∗
          ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((idStoreVt + 0x18#64) ↦₆₄ᵣ getIdKpShimAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = idStorePtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = v_b0 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
          0x36ac#64) := by
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xd5c 0xd74
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x3630 0x363c
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x3694 0x36a8
  dsimp only [trTrapProgAt] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have hadrp0 := (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.adrp_logLevel_0xd64 hb hentry).1
  have hadrp := (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.adrp_logLevel_0xd64 hb hentry).2
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = ctSlicePtr := hx21
  have h5b810 : (b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) = b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by bv_arith
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg4_none_64_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr msgPtr ctxPtr idStorePtr idStoreVt getIdKpShimAddr
    ctSlicePtr v_b0 u_488 : BitVec 64)
    (opkId : BitVec 32) (b_4b0 : BitVec 8)
    (hb : b &&& 0xfff#64 = 0#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xd5c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = ctSlicePtr) :
    SepWP (tripleRatchetProgAt b C ctl abs) getIdKpShimAddr s
      (((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
       ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x488#64) ↦₆₄ u_488) ∗
       ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
       ((msgPtr + 0x78#64) ↦₃₂ 0#32) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((idStoreVt + 0x18#64) ↦₆₄ᵣ getIdKpShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
          ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((coroPtr + 0x488#64) ↦₆₄ ctSlicePtr) ∗
          ((coroPtr + 0x4b0#64) ↦₈ 0#8) ∗
          ((msgPtr + 0x78#64) ↦₃₂ 0#32) ∗
          ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((idStoreVt + 0x18#64) ↦₆₄ᵣ getIdKpShimAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = idStorePtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = v_b0 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
          0x36ac#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg4_none_64_wp_trap b C abs s
      coroPtr msgPtr ctxPtr idStorePtr idStoreVt getIdKpShimAddr
      ctSlicePtr v_b0 u_488 opkId b_4b0 hb hpc hrun hsp_align hx19 hx21)

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg4a_64_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr msgPtr ctxPtr preKeyStorePtr preKeyStoreVt opkLoadShimAddr
    ctSlicePtr u_488 : BitVec 64)
    (opkId : BitVec 32)
    (hb : b &&& 0xfff#64 = 0#64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xd5c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = ctSlicePtr) :
    SepWP (trTrapProgAt b C abs) opkLoadShimAddr s
      (((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗
       ((coroPtr + 0x410#64) ↦₆₄ preKeyStoreVt) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x488#64) ↦₆₄ u_488) ∗
       ((msgPtr + 0x78#64) ↦₃₂ 1#32) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((preKeyStoreVt + 0x18#64) ↦₆₄ᵣ opkLoadShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗
          ((coroPtr + 0x410#64) ↦₆₄ preKeyStoreVt) ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((coroPtr + 0x488#64) ↦₆₄ ctSlicePtr) ∗
          ((msgPtr + 0x78#64) ↦₃₂ 1#32) ∗
          ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((preKeyStoreVt + 0x18#64) ↦₆₄ᵣ opkLoadShimAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = preKeyStorePtr ∧
        s1.readReg64 .x1 = opkId.zeroExtend 64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = opkId.zeroExtend 64 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
          0xdec#64) := by
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xd5c 0xd80
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xdd8 0xde8
  dsimp only [trTrapProgAt] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have hadrp0 := (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.adrp_logLevel_0xd64 hb hentry).1
  have hadrp := (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.adrp_logLevel_0xd64 hb hentry).2
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = ctSlicePtr := hx21
  have h5b810 : (b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) = b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by bv_arith
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P2.4a (`+0x0d5c -> opkLoadShimAddr`, 64-bit `x21 = ctSlicePtr` variant): Stores `ctSlicePtr` at `[coroPtr + 0x488]`, loads `(1#32, opkId)` from `[msgPtr + 0x78..0x7c]`,
restores `x27 = ctxPtr`, branches to `+0x0dd8`,
  loads `opkLoadShimAddr` from `[preKeyStoreVt + 0x18]`,
sets `x0 = preKeyStorePtr`, `x1 = opkId.zeroExtend 64`, and calls `blr x8` at `+0x0de8`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg4a_64_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr msgPtr ctxPtr preKeyStorePtr preKeyStoreVt opkLoadShimAddr
    ctSlicePtr u_488 : BitVec 64)
    (opkId : BitVec 32)
    (hb : b &&& 0xfff#64 = 0#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xd5c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = ctSlicePtr) :
    SepWP (tripleRatchetProgAt b C ctl abs) opkLoadShimAddr s
      (((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗
       ((coroPtr + 0x410#64) ↦₆₄ preKeyStoreVt) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x488#64) ↦₆₄ u_488) ∗
       ((msgPtr + 0x78#64) ↦₃₂ 1#32) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((preKeyStoreVt + 0x18#64) ↦₆₄ᵣ opkLoadShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗
          ((coroPtr + 0x410#64) ↦₆₄ preKeyStoreVt) ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((coroPtr + 0x488#64) ↦₆₄ ctSlicePtr) ∗
          ((msgPtr + 0x78#64) ↦₃₂ 1#32) ∗
          ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((preKeyStoreVt + 0x18#64) ↦₆₄ᵣ opkLoadShimAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = preKeyStorePtr ∧
        s1.readReg64 .x1 = opkId.zeroExtend 64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = opkId.zeroExtend 64 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
          0xdec#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg4a_64_wp_trap b C abs s
      coroPtr msgPtr ctxPtr preKeyStorePtr preKeyStoreVt opkLoadShimAddr
      ctSlicePtr u_488 opkId hb hpc hrun hsp_align hx19 hx21)

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg4c_33_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr ctxPtr opkFutPtr opkFutVt opkDropAddr
    opkPubPtr opkPubCap opkSecPtr opkSecCap opkIdWord u_ac8
    v_98 v_a0 v_b0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 : BitVec 64)
    (hdrop_nz : opkDropAddr ≠ 0#64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x9c4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = v_a0)
    (hx26 : s.readReg64 .x26 = v_98)
    (hx27 : s.readReg64 .x27 = ctxPtr) :
    SepWP (trTrapProgAt b C abs) opkDropAddr s
      (preKeyRecordOut64At (s.sp + 0xa90#64) 33#64 opkPubPtr 33#64 opkPubCap
         opkSecPtr opkSecCap opkIdWord u_ac8 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ opkFutVt) ∗
       ((opkFutVt + 0x0#64) ↦₆₄ᵣ opkDropAddr) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0))
      (fun s1 P_f =>
        (P_f ⊢
          preKeyRecordOut64At (s.sp + 0xa90#64) 33#64 opkPubPtr 33#64 opkPubCap
            opkSecPtr opkSecCap opkIdWord u_ac8 ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ opkFutVt) ∗
          ((opkFutVt + 0x0#64) ↦₆₄ᵣ opkDropAddr) ∗
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xa8#64) ↦₆₄ opkSecCap) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ opkPubCap) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((s.sp + 0xd0#64) ↦₆₄ opkSecPtr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = opkFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = opkFutPtr ∧
        s1.readReg64 .x22 = 33#64 ∧
        s1.readReg64 .x23 = 33#64 ∧
        s1.readReg64 .x24 = opkFutVt ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = opkPubPtr ∧
        s1.readReg64 .x27 = opkIdWord ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
          0xe40#64) := by
  have hdrop_beq : (opkDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x9c4 0x9cc
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xdfc 0xe3c
  dsimp only [trTrapProgAt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = v_b0 := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = v_a0 := hx23
  have hx26' : s.readReg64 (Reg.gpr 26#5) = v_98 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = ctxPtr := hx27
  dsimp only [preKeyRecordOut64At]
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

/-- Segment P2.4c (`pubLen = 33#64` at `+0x10` variant): Reads `Poll::Ready(Ok(PreKeyRecord))` from `sp + 0xa90..0xac8` with `pubLen = 33#64` at `+0x10`,
saves `x26, x23, x21, x27` and `opkPubCap, opkSecPtr, opkSecCap` to stack slots `sp + 0x98..0xd0`,
loads `opkDropAddr` from `[opkFutVt + 0x0]`, sets `x0 = opkFutPtr`,
  and calls `blr x8` at `+0x0e3c`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg4c_33_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr ctxPtr opkFutPtr opkFutVt opkDropAddr
    opkPubPtr opkPubCap opkSecPtr opkSecCap opkIdWord u_ac8
    v_98 v_a0 v_b0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 : BitVec 64)
    (hdrop_nz : opkDropAddr ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x9c4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = v_a0)
    (hx26 : s.readReg64 .x26 = v_98)
    (hx27 : s.readReg64 .x27 = ctxPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs) opkDropAddr s
      (preKeyRecordOut64At (s.sp + 0xa90#64) 33#64 opkPubPtr 33#64 opkPubCap
         opkSecPtr opkSecCap opkIdWord u_ac8 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ opkFutVt) ∗
       ((opkFutVt + 0x0#64) ↦₆₄ᵣ opkDropAddr) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0))
      (fun s1 P_f =>
        (P_f ⊢
          preKeyRecordOut64At (s.sp + 0xa90#64) 33#64 opkPubPtr 33#64 opkPubCap
            opkSecPtr opkSecCap opkIdWord u_ac8 ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ opkFutVt) ∗
          ((opkFutVt + 0x0#64) ↦₆₄ᵣ opkDropAddr) ∗
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xa8#64) ↦₆₄ opkSecCap) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ opkPubCap) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((s.sp + 0xd0#64) ↦₆₄ opkSecPtr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = opkFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = opkFutPtr ∧
        s1.readReg64 .x22 = 33#64 ∧
        s1.readReg64 .x23 = 33#64 ∧
        s1.readReg64 .x24 = opkFutVt ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = opkPubPtr ∧
        s1.readReg64 .x27 = opkIdWord ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
          0xe40#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg4c_33_wp_trap b C abs s
      coroPtr ctxPtr opkFutPtr opkFutVt opkDropAddr
      opkPubPtr opkPubCap opkSecPtr opkSecCap opkIdWord u_ac8
      v_98 v_a0 v_b0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0
      hdrop_nz hpc hrun hsp_align hx19 hx21 hx23 hx26 hx27)

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg4d_33_wp_trap {A : RustAlloc} (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr opkFutPtr opkFutVt opkPubPtr opkPubCap opkSecPtr opkSecCap opkIdWord
    r0 r1 r2 r3 r4 r5 r6 : BitVec 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xe40#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = opkFutPtr)
    (hx22 : s.readReg64 .x22 = 33#64)
    (hx23 : s.readReg64 .x23 = 33#64)
    (hx24 : s.readReg64 .x24 = opkFutVt)
    (hx26 : s.readReg64 .x26 = opkPubPtr)
    (hx27 : s.readReg64 .x27 = opkIdWord) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::key_pair" - ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64)) s
      (((opkFutVt + 0x8#64) ↦₆₄ᵣ 16#64) ∗
       ((opkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live opkFutPtr 16 8 ∗
       memRegion opkFutPtr 16 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((s.sp + 0xa8#64) ↦₆₄ opkSecCap) ∗
       ((s.sp + 0xb8#64) ↦₆₄ opkPubCap) ∗
       ((s.sp + 0xd0#64) ↦₆₄ opkSecPtr) ∗
       ((s.sp + 0x930#64) ↦₆₄ r0) ∗
       ((s.sp + 0x938#64) ↦₆₄ r1) ∗
       ((s.sp + 0x940#64) ↦₆₄ r2) ∗
       ((s.sp + 0x948#64) ↦₆₄ r3) ∗
       ((s.sp + 0x950#64) ↦₆₄ r4) ∗
       ((s.sp + 0x958#64) ↦₆₄ r5) ∗
       ((s.sp + 0x960#64) ↦₆₄ r6))
      (fun s1 P_f =>
        (P_f ⊢
          ((opkFutVt + 0x8#64) ↦₆₄ᵣ 16#64) ∗
          ((opkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((s.sp + 0xa8#64) ↦₆₄ opkSecCap) ∗
          ((s.sp + 0xb8#64) ↦₆₄ opkPubCap) ∗
          ((s.sp + 0xd0#64) ↦₆₄ opkSecPtr) ∗
          ((s.sp + 0x930#64) ↦₆₄ 33#64) ∗
          ((s.sp + 0x938#64) ↦₆₄ opkPubPtr) ∗
          ((s.sp + 0x940#64) ↦₆₄ 33#64) ∗
          ((s.sp + 0x948#64) ↦₆₄ opkPubCap) ∗
          ((s.sp + 0x950#64) ↦₆₄ opkSecPtr) ∗
          ((s.sp + 0x958#64) ↦₆₄ opkSecCap) ∗
          ((s.sp + 0x960#64) ↦₆₄ opkIdWord)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x930#64 ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = opkFutPtr ∧
        s1.readReg64 .x22 = 33#64 ∧
        s1.readReg64 .x23 = 33#64 ∧
        s1.readReg64 .x24 = opkFutVt ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = opkPubPtr ∧
        s1.readReg64 .x27 = opkIdWord ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
          0xe90#64) := by
  have hdealloc := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_dealloc_ok_trap (b := b) (C := C)
    (abs := abs) hA
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xe40 0xe8c
  dsimp only [trTrapProgAt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = opkFutPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = 33#64 := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = 33#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = opkFutVt := hx24
  have hx26' : s.readReg64 (Reg.gpr 26#5) = opkPubPtr := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = opkIdWord := hx27
  wp_steps
  wp_call hdealloc (opkFutPtr, 16, 8)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P2.4d (`x23 = 33#64` variant): Deallocates `opkFutPtr` (`__rust_dealloc`), checks `x22 = 33 ≠ -1`, writes `PreKeyRecord`
to `sp + 0x930..0x968` with `[sp + 0x940] = 33#64`, sets `x0 = sp + 0x930`, `x8 = sp + 0x3e0`,
and calls `bl 0x1e9f8` (`PreKeyRecord::key_pair`) at `+0x0e8c`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg4d_33_wp {A : RustAlloc} (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr opkFutPtr opkFutVt opkPubPtr opkPubCap opkSecPtr opkSecCap opkIdWord
    r0 r1 r2 r3 r4 r5 r6 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xe40#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = opkFutPtr)
    (hx22 : s.readReg64 .x22 = 33#64)
    (hx23 : s.readReg64 .x23 = 33#64)
    (hx24 : s.readReg64 .x24 = opkFutVt)
    (hx26 : s.readReg64 .x26 = opkPubPtr)
    (hx27 : s.readReg64 .x27 = opkIdWord) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::key_pair" - ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64)) s
      (((opkFutVt + 0x8#64) ↦₆₄ᵣ 16#64) ∗
       ((opkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live opkFutPtr 16 8 ∗
       memRegion opkFutPtr 16 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((s.sp + 0xa8#64) ↦₆₄ opkSecCap) ∗
       ((s.sp + 0xb8#64) ↦₆₄ opkPubCap) ∗
       ((s.sp + 0xd0#64) ↦₆₄ opkSecPtr) ∗
       ((s.sp + 0x930#64) ↦₆₄ r0) ∗
       ((s.sp + 0x938#64) ↦₆₄ r1) ∗
       ((s.sp + 0x940#64) ↦₆₄ r2) ∗
       ((s.sp + 0x948#64) ↦₆₄ r3) ∗
       ((s.sp + 0x950#64) ↦₆₄ r4) ∗
       ((s.sp + 0x958#64) ↦₆₄ r5) ∗
       ((s.sp + 0x960#64) ↦₆₄ r6))
      (fun s1 P_f =>
        (P_f ⊢
          ((opkFutVt + 0x8#64) ↦₆₄ᵣ 16#64) ∗
          ((opkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((s.sp + 0xa8#64) ↦₆₄ opkSecCap) ∗
          ((s.sp + 0xb8#64) ↦₆₄ opkPubCap) ∗
          ((s.sp + 0xd0#64) ↦₆₄ opkSecPtr) ∗
          ((s.sp + 0x930#64) ↦₆₄ 33#64) ∗
          ((s.sp + 0x938#64) ↦₆₄ opkPubPtr) ∗
          ((s.sp + 0x940#64) ↦₆₄ 33#64) ∗
          ((s.sp + 0x948#64) ↦₆₄ opkPubCap) ∗
          ((s.sp + 0x950#64) ↦₆₄ opkSecPtr) ∗
          ((s.sp + 0x958#64) ↦₆₄ opkSecCap) ∗
          ((s.sp + 0x960#64) ↦₆₄ opkIdWord)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x930#64 ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = opkFutPtr ∧
        s1.readReg64 .x22 = 33#64 ∧
        s1.readReg64 .x23 = 33#64 ∧
        s1.readReg64 .x24 = opkFutVt ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = opkPubPtr ∧
        s1.readReg64 .x27 = opkIdWord ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
          0xe90#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg4d_33_wp_trap b C abs hA s
      coroPtr opkFutPtr opkFutVt opkPubPtr opkPubCap opkSecPtr opkSecCap opkIdWord
      r0 r1 r2 r3 r4 r5 r6
      hpc hrun hsp_align hx19 hx21 hx22 hx23 hx24 hx26 hx27)

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_err3b_1568_wp_trap {A : RustAlloc} (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr opkFutPtr opkFutVt kyberKpPubPtr kyberKpSecPtr errTag outPtr
    v_a8 v_b8 : BitVec 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xe40#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = opkFutPtr)
    (hx22 : s.readReg64 .x22 = 0xffffffffffffffff#64)
    (hx24 : s.readReg64 .x24 = opkFutVt)
    (hx26 : s.readReg64 .x26 = errTag)
    (hx28 : s.readReg64 .x28 = s.sp + 0xa90#64) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1648#64) s
      (((opkFutVt + 0x8#64) ↦₆₄ᵣ 16#64) ∗
       ((opkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live opkFutPtr 16 8 ∗
       memRegion opkFutPtr 16 ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ kyberKpPubPtr) ∗
       ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ kyberKpSecPtr) ∗
       ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
       A.live kyberKpPubPtr 1568 1 ∗
       memRegion kyberKpPubPtr 1568 ∗
       A.live kyberKpSecPtr 3168 1 ∗
       memRegion kyberKpSecPtr 3168 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗
       ((s.sp + 0xa8#64) ↦₆₄ v_a8) ∗
       ((s.sp + 0xb8#64) ↦₆₄ v_b8) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr))
      (fun s1 P_f =>
        (P_f ⊢
          ((opkFutVt + 0x8#64) ↦₆₄ᵣ 16#64) ∗
          ((opkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          ((coroPtr + 0x3d8#64) ↦₆₄ kyberKpPubPtr) ∗
          ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
          ((coroPtr + 0x3e8#64) ↦₆₄ kyberKpSecPtr) ∗
          ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
          ((s.sp + 0xa8#64) ↦₆₄ v_a8) ∗
          ((s.sp + 0xb8#64) ↦₆₄ v_b8) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = errTag ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  have hdealloc := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_dealloc_ok_trap (b := b) (C := C)
    (abs := abs) hA
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xe40 0xe58
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x146c 0x1484
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x160c 0x1644
  dsimp only [trTrapProgAt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = opkFutPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = 0xffffffffffffffff#64 := hx22
  have hx24' : s.readReg64 (Reg.gpr 24#5) = opkFutVt := hx24
  have hx26' : s.readReg64 (Reg.gpr 26#5) = errTag := hx26
  have hx28' : s.readReg64 (Reg.gpr 28#5) = s.sp + 0xa90#64 := hx28
  wp_steps
  wp_call hdealloc (opkFutPtr, 16, 8)
  wp_steps
  wp_call hdealloc (kyberKpPubPtr, 1568, 1)
  wp_steps
  rw [hsp_sf]
  wp_call hdealloc (kyberKpSecPtr, 3168, 1)
  wp_steps
  rw [hsp_sf_1, hsp_sf]
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- Segment P2.Err3b (`+0x0e40 -> +0x1648`, `1568`/`3168` Kyber KeyPair dealloc sizes): Deallocates `opkFutPtr` (`16, 8`), `kyberKpPubPtr` (`1568, 1`), and `kyberKpSecPtr` (`3168, 1`),
sets `[coroPtr + 0x4f1] = 0#8`, loads `x26 = [sp + 0xc8] = outPtr`, and reaches `+0x1648`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_err3b_1568_wp {A : RustAlloc} (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr opkFutPtr opkFutVt kyberKpPubPtr kyberKpSecPtr errTag outPtr
    v_a8 v_b8 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xe40#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = opkFutPtr)
    (hx22 : s.readReg64 .x22 = 0xffffffffffffffff#64)
    (hx24 : s.readReg64 .x24 = opkFutVt)
    (hx26 : s.readReg64 .x26 = errTag)
    (hx28 : s.readReg64 .x28 = s.sp + 0xa90#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1648#64) s
      (((opkFutVt + 0x8#64) ↦₆₄ᵣ 16#64) ∗
       ((opkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live opkFutPtr 16 8 ∗
       memRegion opkFutPtr 16 ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ kyberKpPubPtr) ∗
       ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ kyberKpSecPtr) ∗
       ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
       A.live kyberKpPubPtr 1568 1 ∗
       memRegion kyberKpPubPtr 1568 ∗
       A.live kyberKpSecPtr 3168 1 ∗
       memRegion kyberKpSecPtr 3168 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗
       ((s.sp + 0xa8#64) ↦₆₄ v_a8) ∗
       ((s.sp + 0xb8#64) ↦₆₄ v_b8) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr))
      (fun s1 P_f =>
        (P_f ⊢
          ((opkFutVt + 0x8#64) ↦₆₄ᵣ 16#64) ∗
          ((opkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          ((coroPtr + 0x3d8#64) ↦₆₄ kyberKpPubPtr) ∗
          ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
          ((coroPtr + 0x3e8#64) ↦₆₄ kyberKpSecPtr) ∗
          ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
          ((s.sp + 0xa8#64) ↦₆₄ v_a8) ∗
          ((s.sp + 0xb8#64) ↦₆₄ v_b8) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = errTag ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_err3b_1568_wp_trap b C abs hA s
      coroPtr opkFutPtr opkFutVt kyberKpPubPtr kyberKpSecPtr errTag outPtr
      v_a8 v_b8 hpc hrun hsp_align hx19 hx21 hx22 hx24 hx26 hx28)

end CryptoVerification.E2E.Pqxdh.ResponderClosure
