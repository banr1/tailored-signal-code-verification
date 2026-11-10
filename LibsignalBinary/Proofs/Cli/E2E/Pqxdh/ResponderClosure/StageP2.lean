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
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP2 -- shake: keep

/-!
# Responder Closure Stages P2.5 and P2.6 (`+0x36ac → +0x1778`)

Symbolic-execution segment proofs for the second half of Stage P2 of the CLI responder prekey
decryption closure, covering local identity key-pair retrieval, `IdentityKey::is_same_account`,
`initialize_bob_session`, local registration ID lookup, `SessionRecord::promote_state`, and entry
into the Stage P3 decryption frame (`+0x1778`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000

set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")

/-! ## 1. Stage P2.5 Segment Proofs (`+0x36ac → +0x1258`) -/

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg5a_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr ctxPtr idKpFutPtr idKpFutVt idKpPollAddr u_4f8 u_500 : BitVec 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x36ac#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = idKpFutPtr)
    (hx1 : s.readReg64 .x1 = idKpFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr) :
    SepWP (trTrapProgAt b C abs) idKpPollAddr s
      (((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗
       ((coroPtr + 0x500#64) ↦₆₄ u_500) ∗
       ((idKpFutVt + 0x18#64) ↦₆₄ᵣ idKpPollAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x4f8#64) ↦₆₄ idKpFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ idKpFutVt) ∗
          ((idKpFutVt + 0x18#64) ↦₆₄ᵣ idKpPollAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = idKpFutPtr ∧
        s1.readReg64 .x1 = ctxPtr ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x7bc#64) := by
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x36ac 0x36b4
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x7ac 0x7b8
  dsimp only [trTrapProgAt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = idKpFutPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = idKpFutVt := hx1
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx27' : s.readReg64 (Reg.gpr 27#5) = ctxPtr := hx27
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- Segment P2.5a (`+0x36ac → +0x07b8`): stores `(idKpFutPtr, idKpFutVt)` at `coroPtr + 0x4f8..0x500`
and polls `get_identity_key_pair` (`blr x9`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg5a_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr ctxPtr idKpFutPtr idKpFutVt idKpPollAddr u_4f8 u_500 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x36ac#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = idKpFutPtr)
    (hx1 : s.readReg64 .x1 = idKpFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs) idKpPollAddr s
      (((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗
       ((coroPtr + 0x500#64) ↦₆₄ u_500) ∗
       ((idKpFutVt + 0x18#64) ↦₆₄ᵣ idKpPollAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x4f8#64) ↦₆₄ idKpFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ idKpFutVt) ∗
          ((idKpFutVt + 0x18#64) ↦₆₄ᵣ idKpPollAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = idKpFutPtr ∧
        s1.readReg64 .x1 = ctxPtr ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x7bc#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg5a_wp_trap b C abs s coroPtr
      ctxPtr idKpFutPtr idKpFutVt idKpPollAddr u_4f8 u_500 hpc hrun hx0 hx1 hx19 hx27)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg5c1_wp_trap {A : RustAlloc} (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr msgPtr remoteAddrPtr localAddrPtr idKpFutPtr idKpFutVt
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
    (hx29 : s.readReg64 .x29 = s.sp + 0xc10#64) :
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
       ((s.sp + 0xb90#64) ↦₆₄ w6) ∗
       ((s.sp + 0xb98#64) ↦₈ b63) ∗
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
          ((s.sp + 0xb90#64) ↦₆₄ w6) ∗
          ((s.sp + 0xb98#64) ↦₈ b63) ∗
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
        s1.readReg64 .x29 = s.sp + 0xc10#64) := by
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
  have hx29' : s.readReg64 (Reg.gpr 29#5) = s.sp + 0xc10#64 := hx29
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
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

/-- Segment P2.5c1 (`+0x0ac4 → +0x114c`): deallocates `idKpFutPtr` and writes the first 55 bytes of
`IdentityKeyPair` into `coroPtr + 0x798..0x7ce`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg5c1_wp {A : RustAlloc} (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr msgPtr remoteAddrPtr localAddrPtr idKpFutPtr idKpFutVt
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
    (hx29 : s.readReg64 .x29 = s.sp + 0xc10#64) :
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
       ((s.sp + 0xb90#64) ↦₆₄ w6) ∗
       ((s.sp + 0xb98#64) ↦₈ b63) ∗
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
          ((s.sp + 0xb90#64) ↦₆₄ w6) ∗
          ((s.sp + 0xb98#64) ↦₈ b63) ∗
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
        s1.readReg64 .x29 = s.sp + 0xc10#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg5c1_wp_trap b C abs hA s coroPtr
      msgPtr remoteAddrPtr localAddrPtr idKpFutPtr idKpFutVt kyberPreKeyId64
      w0 w1 w2 w3 w4 w5 w6 cw0 cw1 cw2 cw3 cw4 cw5 opkId
      b0 b1 b2 b3 b4 b5 b6 b63 c0 c1 c2 c3 c4 c5 c6
      hpc hrun hsp_align hx19 hx20 hx21 hx22 hx23 hx24 hx27 hx29)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg5c2_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr msgPtr ik0 ik1 ik2 ik3 w6 cw6
    u_930 u_938 u_940 u_948 : BitVec 64)
    (b63 c63 opk_b64 : BitVec 8)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x114c#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = b63.zeroExtend 64)
    (hx9 : s.readReg64 .x9 = w6)
    (hx10 : s.readReg64 .x10 = coroPtr + 0x798#64)
    (hx11 : s.readReg64 .x11 = coroPtr + 0x7cf#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx23 : s.readReg64 .x23 = s.sp + 0x930#64) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1168#64) s
      (((coroPtr + 0x798#64) ↦₆₄ ik0) ∗
       ((coroPtr + 0x7a0#64) ↦₆₄ ik1) ∗
       ((coroPtr + 0x7a8#64) ↦₆₄ ik2) ∗
       ((coroPtr + 0x7b0#64) ↦₆₄ ik3) ∗
       ((coroPtr + 0x7cf#64) ↦₆₄ cw6) ∗
       ((coroPtr + 0x7d7#64) ↦₈ c63) ∗
       ((coroPtr + 0x4f0#64) ↦₈ opk_b64) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((s.sp + 0x930#64) ↦₆₄ u_930) ∗
       ((s.sp + 0x938#64) ↦₆₄ u_938) ∗
       ((s.sp + 0x940#64) ↦₆₄ u_940) ∗
       ((s.sp + 0x948#64) ↦₆₄ u_948))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x798#64) ↦₆₄ ik0) ∗
          ((coroPtr + 0x7a0#64) ↦₆₄ ik1) ∗
          ((coroPtr + 0x7a8#64) ↦₆₄ ik2) ∗
          ((coroPtr + 0x7b0#64) ↦₆₄ ik3) ∗
          ((coroPtr + 0x7cf#64) ↦₆₄ w6) ∗
          ((coroPtr + 0x7d7#64) ↦₈ b63) ∗
          ((coroPtr + 0x4f0#64) ↦₈ opk_b64) ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((s.sp + 0x930#64) ↦₆₄ ik0) ∗
          ((s.sp + 0x938#64) ↦₆₄ ik1) ∗
          ((s.sp + 0x940#64) ↦₆₄ ik2) ∗
          ((s.sp + 0x948#64) ↦₆₄ ik3)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.readReg64 .x0 ∧
        s1.readReg64 .x1 = s.readReg64 .x1 ∧
        s1.readReg64 .x2 = msgPtr + 0xc8#64 ∧
        s1.readReg64 .x3 = s.readReg64 .x3 ∧
        s1.readReg64 .x8 = opk_b64.zeroExtend 64 ∧
        s1.readReg64 .x9 = msgPtr ∧
        s1.readReg64 .x10 = coroPtr + 0x798#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.sp + 0x930#64 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x114c 0x1164
  dsimp only [trTrapProgAt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx8' : s.readReg64 (Reg.gpr 8#5) = b63.zeroExtend 64 := hx8
  have hx9' : s.readReg64 (Reg.gpr 9#5) = w6 := hx9
  have hx10' : s.readReg64 (Reg.gpr 10#5) = coroPtr + 0x798#64 := hx10
  have hx11' : s.readReg64 (Reg.gpr 11#5) = coroPtr + 0x7cf#64 := hx11
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx23' : s.readReg64 (Reg.gpr 23#5) = s.sp + 0x930#64 := hx23
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P2.5c2 (`+0x114c → +0x1168`): writes the remaining `IdentityKeyPair` bytes to
`coroPtr + 0x7cf..0x7d7` and copies the first 32 bytes to `sp + 0x930..0x94f`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg5c2_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr msgPtr ik0 ik1 ik2 ik3 w6 cw6
    u_930 u_938 u_940 u_948 : BitVec 64)
    (b63 c63 opk_b64 : BitVec 8)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x114c#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = b63.zeroExtend 64)
    (hx9 : s.readReg64 .x9 = w6)
    (hx10 : s.readReg64 .x10 = coroPtr + 0x798#64)
    (hx11 : s.readReg64 .x11 = coroPtr + 0x7cf#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx23 : s.readReg64 .x23 = s.sp + 0x930#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1168#64) s
      (((coroPtr + 0x798#64) ↦₆₄ ik0) ∗
       ((coroPtr + 0x7a0#64) ↦₆₄ ik1) ∗
       ((coroPtr + 0x7a8#64) ↦₆₄ ik2) ∗
       ((coroPtr + 0x7b0#64) ↦₆₄ ik3) ∗
       ((coroPtr + 0x7cf#64) ↦₆₄ cw6) ∗
       ((coroPtr + 0x7d7#64) ↦₈ c63) ∗
       ((coroPtr + 0x4f0#64) ↦₈ opk_b64) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((s.sp + 0x930#64) ↦₆₄ u_930) ∗
       ((s.sp + 0x938#64) ↦₆₄ u_938) ∗
       ((s.sp + 0x940#64) ↦₆₄ u_940) ∗
       ((s.sp + 0x948#64) ↦₆₄ u_948))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x798#64) ↦₆₄ ik0) ∗
          ((coroPtr + 0x7a0#64) ↦₆₄ ik1) ∗
          ((coroPtr + 0x7a8#64) ↦₆₄ ik2) ∗
          ((coroPtr + 0x7b0#64) ↦₆₄ ik3) ∗
          ((coroPtr + 0x7cf#64) ↦₆₄ w6) ∗
          ((coroPtr + 0x7d7#64) ↦₈ b63) ∗
          ((coroPtr + 0x4f0#64) ↦₈ opk_b64) ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((s.sp + 0x930#64) ↦₆₄ ik0) ∗
          ((s.sp + 0x938#64) ↦₆₄ ik1) ∗
          ((s.sp + 0x940#64) ↦₆₄ ik2) ∗
          ((s.sp + 0x948#64) ↦₆₄ ik3)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.readReg64 .x0 ∧
        s1.readReg64 .x1 = s.readReg64 .x1 ∧
        s1.readReg64 .x2 = msgPtr + 0xc8#64 ∧
        s1.readReg64 .x3 = s.readReg64 .x3 ∧
        s1.readReg64 .x8 = opk_b64.zeroExtend 64 ∧
        s1.readReg64 .x9 = msgPtr ∧
        s1.readReg64 .x10 = coroPtr + 0x798#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.sp + 0x930#64 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg5c2_wp_trap b C abs s coroPtr
      msgPtr ik0 ik1 ik2 ik3 w6 cw6 u_930 u_938 u_940 u_948
      b63 c63 opk_b64 hpc hrun hx8 hx9 hx10 hx11 hx19 hx23)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg5c3_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr msgPtr localAddrPtr remoteAddrPtr
    ik4 ik5 ik6 ik7
    spk0 spk1 spk2 spk3 spk4 spk5 spk6 spk7
    opk0 opk1 opk2 opk3 opk4 opk5 opk6 opk7
    kyb0 kyb1 kyb2 kyb3
    ikA0 ikA1 ikA2 ikA3
    ekA0 ekA1 ekA2 ekA3
    u_950 u_958 u_960 u_968
    u_a90 u_a98 u_aa0 u_aa8 u_ab0 u_ab8 u_ac0 u_ac8
    u_3e0 u_3e8 u_3f0 u_3f8 u_400 u_408 u_410 u_418
    u_560 u_568 u_570 u_578
    u_6a0 u_6a8 u_6b0 u_6b8
    u_7e0 u_7e8 u_7f0 u_7f8 : BitVec 64)
    (opk_b64 u_420 b_4f1 : BitVec 8)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1168#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = coroPtr + 0x798#64)
    (hx1 : s.readReg64 .x1 = localAddrPtr)
    (hx2 : s.readReg64 .x2 = msgPtr + 0xc8#64)
    (hx3 : s.readReg64 .x3 = remoteAddrPtr)
    (hx8 : s.readReg64 .x8 = opk_b64.zeroExtend 64)
    (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = coroPtr + 0x798#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = s.sp + 0x370#64)
    (hx23 : s.readReg64 .x23 = s.sp + 0x930#64)
    (hx24 : s.readReg64 .x24 = coroPtr + 0x398#64)
    (hx28 : s.readReg64 .x28 = s.sp + 0xa90#64) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account" - ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64)) s
      (((coroPtr + 0x7b8#64) ↦₆₄ ik4) ∗
       ((coroPtr + 0x7c0#64) ↦₆₄ ik5) ∗
       ((coroPtr + 0x7c8#64) ↦₆₄ ik6) ∗
       ((coroPtr + 0x7d0#64) ↦₆₄ ik7) ∗
       ((coroPtr + 0x398#64) ↦₆₄ spk0) ∗
       ((coroPtr + 0x3a0#64) ↦₆₄ spk1) ∗
       ((coroPtr + 0x3a8#64) ↦₆₄ spk2) ∗
       ((coroPtr + 0x3b0#64) ↦₆₄ spk3) ∗
       ((coroPtr + 0x3b8#64) ↦₆₄ spk4) ∗
       ((coroPtr + 0x3c0#64) ↦₆₄ spk5) ∗
       ((coroPtr + 0x3c8#64) ↦₆₄ spk6) ∗
       ((coroPtr + 0x3d0#64) ↦₆₄ spk7) ∗
       ((coroPtr + 0x4b0#64) ↦₆₄ opk0) ∗
       ((coroPtr + 0x4b8#64) ↦₆₄ opk1) ∗
       ((coroPtr + 0x4c0#64) ↦₆₄ opk2) ∗
       ((coroPtr + 0x4c8#64) ↦₆₄ opk3) ∗
       ((coroPtr + 0x4d0#64) ↦₆₄ opk4) ∗
       ((coroPtr + 0x4d8#64) ↦₆₄ opk5) ∗
       ((coroPtr + 0x4e0#64) ↦₆₄ opk6) ∗
       ((coroPtr + 0x4e8#64) ↦₆₄ opk7) ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ kyb0) ∗
       ((coroPtr + 0x3e0#64) ↦₆₄ kyb1) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ kyb2) ∗
       ((coroPtr + 0x3f0#64) ↦₆₄ kyb3) ∗
       ((msgPtr + 0xa8#64) ↦₆₄ ekA0) ∗
       ((msgPtr + 0xb0#64) ↦₆₄ ekA1) ∗
       ((msgPtr + 0xb8#64) ↦₆₄ ekA2) ∗
       ((msgPtr + 0xc0#64) ↦₆₄ ekA3) ∗
       ((msgPtr + 0xc8#64) ↦₆₄ ikA0) ∗
       ((msgPtr + 0xd0#64) ↦₆₄ ikA1) ∗
       ((msgPtr + 0xd8#64) ↦₆₄ ikA2) ∗
       ((msgPtr + 0xe0#64) ↦₆₄ ikA3) ∗
       ((s.sp + 0x950#64) ↦₆₄ u_950) ∗
       ((s.sp + 0x958#64) ↦₆₄ u_958) ∗
       ((s.sp + 0x960#64) ↦₆₄ u_960) ∗
       ((s.sp + 0x968#64) ↦₆₄ u_968) ∗
       ((s.sp + 0xa90#64) ↦₆₄ u_a90) ∗
       ((s.sp + 0xa98#64) ↦₆₄ u_a98) ∗
       ((s.sp + 0xaa0#64) ↦₆₄ u_aa0) ∗
       ((s.sp + 0xaa8#64) ↦₆₄ u_aa8) ∗
       ((s.sp + 0xab0#64) ↦₆₄ u_ab0) ∗
       ((s.sp + 0xab8#64) ↦₆₄ u_ab8) ∗
       ((s.sp + 0xac0#64) ↦₆₄ u_ac0) ∗
       ((s.sp + 0xac8#64) ↦₆₄ u_ac8) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ u_3e0) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ u_3e8) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ u_3f0) ∗
       ((s.sp + 0x3f8#64) ↦₆₄ u_3f8) ∗
       ((s.sp + 0x400#64) ↦₆₄ u_400) ∗
       ((s.sp + 0x408#64) ↦₆₄ u_408) ∗
       ((s.sp + 0x410#64) ↦₆₄ u_410) ∗
       ((s.sp + 0x418#64) ↦₆₄ u_418) ∗
       ((s.sp + 0x420#64) ↦₈ u_420) ∗
       ((s.sp + 0x560#64) ↦₆₄ u_560) ∗
       ((s.sp + 0x568#64) ↦₆₄ u_568) ∗
       ((s.sp + 0x570#64) ↦₆₄ u_570) ∗
       ((s.sp + 0x578#64) ↦₆₄ u_578) ∗
       ((s.sp + 0x6a0#64) ↦₆₄ u_6a0) ∗
       ((s.sp + 0x6a8#64) ↦₆₄ u_6a8) ∗
       ((s.sp + 0x6b0#64) ↦₆₄ u_6b0) ∗
       ((s.sp + 0x6b8#64) ↦₆₄ u_6b8) ∗
       ((s.sp + 0x7e0#64) ↦₆₄ u_7e0) ∗
       ((s.sp + 0x7e8#64) ↦₆₄ u_7e8) ∗
       ((s.sp + 0x7f0#64) ↦₆₄ u_7f0) ∗
       ((s.sp + 0x7f8#64) ↦₆₄ u_7f8))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x7b8#64) ↦₆₄ ik4) ∗
          ((coroPtr + 0x7c0#64) ↦₆₄ ik5) ∗
          ((coroPtr + 0x7c8#64) ↦₆₄ ik6) ∗
          ((coroPtr + 0x7d0#64) ↦₆₄ ik7) ∗
          ((coroPtr + 0x398#64) ↦₆₄ spk0) ∗
          ((coroPtr + 0x3a0#64) ↦₆₄ spk1) ∗
          ((coroPtr + 0x3a8#64) ↦₆₄ spk2) ∗
          ((coroPtr + 0x3b0#64) ↦₆₄ spk3) ∗
          ((coroPtr + 0x3b8#64) ↦₆₄ spk4) ∗
          ((coroPtr + 0x3c0#64) ↦₆₄ spk5) ∗
          ((coroPtr + 0x3c8#64) ↦₆₄ spk6) ∗
          ((coroPtr + 0x3d0#64) ↦₆₄ spk7) ∗
          ((coroPtr + 0x4b0#64) ↦₆₄ opk0) ∗
          ((coroPtr + 0x4b8#64) ↦₆₄ opk1) ∗
          ((coroPtr + 0x4c0#64) ↦₆₄ opk2) ∗
          ((coroPtr + 0x4c8#64) ↦₆₄ opk3) ∗
          ((coroPtr + 0x4d0#64) ↦₆₄ opk4) ∗
          ((coroPtr + 0x4d8#64) ↦₆₄ opk5) ∗
          ((coroPtr + 0x4e0#64) ↦₆₄ opk6) ∗
          ((coroPtr + 0x4e8#64) ↦₆₄ opk7) ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
          ((coroPtr + 0x3d8#64) ↦₆₄ kyb0) ∗
          ((coroPtr + 0x3e0#64) ↦₆₄ kyb1) ∗
          ((coroPtr + 0x3e8#64) ↦₆₄ kyb2) ∗
          ((coroPtr + 0x3f0#64) ↦₆₄ kyb3) ∗
          ((msgPtr + 0xa8#64) ↦₆₄ ekA0) ∗
          ((msgPtr + 0xb0#64) ↦₆₄ ekA1) ∗
          ((msgPtr + 0xb8#64) ↦₆₄ ekA2) ∗
          ((msgPtr + 0xc0#64) ↦₆₄ ekA3) ∗
          ((msgPtr + 0xc8#64) ↦₆₄ ikA0) ∗
          ((msgPtr + 0xd0#64) ↦₆₄ ikA1) ∗
          ((msgPtr + 0xd8#64) ↦₆₄ ikA2) ∗
          ((msgPtr + 0xe0#64) ↦₆₄ ikA3) ∗
          ((s.sp + 0x950#64) ↦₆₄ ik4) ∗
          ((s.sp + 0x958#64) ↦₆₄ ik5) ∗
          ((s.sp + 0x960#64) ↦₆₄ ik6) ∗
          ((s.sp + 0x968#64) ↦₆₄ ik7) ∗
          ((s.sp + 0xa90#64) ↦₆₄ spk0) ∗
          ((s.sp + 0xa98#64) ↦₆₄ spk1) ∗
          ((s.sp + 0xaa0#64) ↦₆₄ spk2) ∗
          ((s.sp + 0xaa8#64) ↦₆₄ spk3) ∗
          ((s.sp + 0xab0#64) ↦₆₄ spk4) ∗
          ((s.sp + 0xab8#64) ↦₆₄ spk5) ∗
          ((s.sp + 0xac0#64) ↦₆₄ spk6) ∗
          ((s.sp + 0xac8#64) ↦₆₄ spk7) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ opk0) ∗
          ((s.sp + 0x3e8#64) ↦₆₄ opk1) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ opk2) ∗
          ((s.sp + 0x3f8#64) ↦₆₄ opk3) ∗
          ((s.sp + 0x400#64) ↦₆₄ opk4) ∗
          ((s.sp + 0x408#64) ↦₆₄ opk5) ∗
          ((s.sp + 0x410#64) ↦₆₄ opk6) ∗
          ((s.sp + 0x418#64) ↦₆₄ opk7) ∗
          ((s.sp + 0x420#64) ↦₈ opk_b64) ∗
          ((s.sp + 0x560#64) ↦₆₄ kyb0) ∗
          ((s.sp + 0x568#64) ↦₆₄ kyb1) ∗
          ((s.sp + 0x570#64) ↦₆₄ kyb2) ∗
          ((s.sp + 0x578#64) ↦₆₄ kyb3) ∗
          ((s.sp + 0x6a0#64) ↦₆₄ ikA0) ∗
          ((s.sp + 0x6a8#64) ↦₆₄ ikA1) ∗
          ((s.sp + 0x6b0#64) ↦₆₄ ikA2) ∗
          ((s.sp + 0x6b8#64) ↦₆₄ ikA3) ∗
          ((s.sp + 0x7e0#64) ↦₆₄ ekA0) ∗
          ((s.sp + 0x7e8#64) ↦₆₄ ekA1) ∗
          ((s.sp + 0x7f0#64) ↦₆₄ ekA2) ∗
          ((s.sp + 0x7f8#64) ↦₆₄ ekA3)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0x798#64 ∧
        s1.readReg64 .x1 = localAddrPtr ∧
        s1.readReg64 .x2 = msgPtr + 0xc8#64 ∧
        s1.readReg64 .x3 = remoteAddrPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = s.sp + 0x370#64 ∧
        s1.readReg64 .x23 = s.sp + 0x930#64 ∧
        s1.readReg64 .x24 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x11d0#64) := by
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1168 0x11cc
  dsimp only [trTrapProgAt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = coroPtr + 0x798#64 := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = localAddrPtr := hx1
  have hx2' : s.readReg64 (Reg.gpr 2#5) = msgPtr + 0xc8#64 := hx2
  have hx3' : s.readReg64 (Reg.gpr 3#5) = remoteAddrPtr := hx3
  have hx8' : s.readReg64 (Reg.gpr 8#5) = opk_b64.zeroExtend 64 := hx8
  have hx9' : s.readReg64 (Reg.gpr 9#5) = msgPtr := hx9
  have hx10' : s.readReg64 (Reg.gpr 10#5) = coroPtr + 0x798#64 := hx10
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = s.sp + 0x370#64 := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = s.sp + 0x930#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = coroPtr + 0x398#64 := hx24
  have hx28' : s.readReg64 (Reg.gpr 28#5) = s.sp + 0xa90#64 := hx28
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P2.5c3 (`+0x1168 → +0x11cc`): stages `IdentityKeyPair`, `spkKp`, `opk`, `kyberKp`,
`message.identity_key`, and `message.base_key` on the stack and calls `IdentityKey::is_same_account`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg5c3_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr msgPtr localAddrPtr remoteAddrPtr
    ik4 ik5 ik6 ik7
    spk0 spk1 spk2 spk3 spk4 spk5 spk6 spk7
    opk0 opk1 opk2 opk3 opk4 opk5 opk6 opk7
    kyb0 kyb1 kyb2 kyb3
    ikA0 ikA1 ikA2 ikA3
    ekA0 ekA1 ekA2 ekA3
    u_950 u_958 u_960 u_968
    u_a90 u_a98 u_aa0 u_aa8 u_ab0 u_ab8 u_ac0 u_ac8
    u_3e0 u_3e8 u_3f0 u_3f8 u_400 u_408 u_410 u_418
    u_560 u_568 u_570 u_578
    u_6a0 u_6a8 u_6b0 u_6b8
    u_7e0 u_7e8 u_7f0 u_7f8 : BitVec 64)
    (opk_b64 u_420 b_4f1 : BitVec 8)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1168#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = coroPtr + 0x798#64)
    (hx1 : s.readReg64 .x1 = localAddrPtr)
    (hx2 : s.readReg64 .x2 = msgPtr + 0xc8#64)
    (hx3 : s.readReg64 .x3 = remoteAddrPtr)
    (hx8 : s.readReg64 .x8 = opk_b64.zeroExtend 64)
    (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = coroPtr + 0x798#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = s.sp + 0x370#64)
    (hx23 : s.readReg64 .x23 = s.sp + 0x930#64)
    (hx24 : s.readReg64 .x24 = coroPtr + 0x398#64)
    (hx28 : s.readReg64 .x28 = s.sp + 0xa90#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account" - ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64)) s
      (((coroPtr + 0x7b8#64) ↦₆₄ ik4) ∗
       ((coroPtr + 0x7c0#64) ↦₆₄ ik5) ∗
       ((coroPtr + 0x7c8#64) ↦₆₄ ik6) ∗
       ((coroPtr + 0x7d0#64) ↦₆₄ ik7) ∗
       ((coroPtr + 0x398#64) ↦₆₄ spk0) ∗
       ((coroPtr + 0x3a0#64) ↦₆₄ spk1) ∗
       ((coroPtr + 0x3a8#64) ↦₆₄ spk2) ∗
       ((coroPtr + 0x3b0#64) ↦₆₄ spk3) ∗
       ((coroPtr + 0x3b8#64) ↦₆₄ spk4) ∗
       ((coroPtr + 0x3c0#64) ↦₆₄ spk5) ∗
       ((coroPtr + 0x3c8#64) ↦₆₄ spk6) ∗
       ((coroPtr + 0x3d0#64) ↦₆₄ spk7) ∗
       ((coroPtr + 0x4b0#64) ↦₆₄ opk0) ∗
       ((coroPtr + 0x4b8#64) ↦₆₄ opk1) ∗
       ((coroPtr + 0x4c0#64) ↦₆₄ opk2) ∗
       ((coroPtr + 0x4c8#64) ↦₆₄ opk3) ∗
       ((coroPtr + 0x4d0#64) ↦₆₄ opk4) ∗
       ((coroPtr + 0x4d8#64) ↦₆₄ opk5) ∗
       ((coroPtr + 0x4e0#64) ↦₆₄ opk6) ∗
       ((coroPtr + 0x4e8#64) ↦₆₄ opk7) ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ kyb0) ∗
       ((coroPtr + 0x3e0#64) ↦₆₄ kyb1) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ kyb2) ∗
       ((coroPtr + 0x3f0#64) ↦₆₄ kyb3) ∗
       ((msgPtr + 0xa8#64) ↦₆₄ ekA0) ∗
       ((msgPtr + 0xb0#64) ↦₆₄ ekA1) ∗
       ((msgPtr + 0xb8#64) ↦₆₄ ekA2) ∗
       ((msgPtr + 0xc0#64) ↦₆₄ ekA3) ∗
       ((msgPtr + 0xc8#64) ↦₆₄ ikA0) ∗
       ((msgPtr + 0xd0#64) ↦₆₄ ikA1) ∗
       ((msgPtr + 0xd8#64) ↦₆₄ ikA2) ∗
       ((msgPtr + 0xe0#64) ↦₆₄ ikA3) ∗
       ((s.sp + 0x950#64) ↦₆₄ u_950) ∗
       ((s.sp + 0x958#64) ↦₆₄ u_958) ∗
       ((s.sp + 0x960#64) ↦₆₄ u_960) ∗
       ((s.sp + 0x968#64) ↦₆₄ u_968) ∗
       ((s.sp + 0xa90#64) ↦₆₄ u_a90) ∗
       ((s.sp + 0xa98#64) ↦₆₄ u_a98) ∗
       ((s.sp + 0xaa0#64) ↦₆₄ u_aa0) ∗
       ((s.sp + 0xaa8#64) ↦₆₄ u_aa8) ∗
       ((s.sp + 0xab0#64) ↦₆₄ u_ab0) ∗
       ((s.sp + 0xab8#64) ↦₆₄ u_ab8) ∗
       ((s.sp + 0xac0#64) ↦₆₄ u_ac0) ∗
       ((s.sp + 0xac8#64) ↦₆₄ u_ac8) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ u_3e0) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ u_3e8) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ u_3f0) ∗
       ((s.sp + 0x3f8#64) ↦₆₄ u_3f8) ∗
       ((s.sp + 0x400#64) ↦₆₄ u_400) ∗
       ((s.sp + 0x408#64) ↦₆₄ u_408) ∗
       ((s.sp + 0x410#64) ↦₆₄ u_410) ∗
       ((s.sp + 0x418#64) ↦₆₄ u_418) ∗
       ((s.sp + 0x420#64) ↦₈ u_420) ∗
       ((s.sp + 0x560#64) ↦₆₄ u_560) ∗
       ((s.sp + 0x568#64) ↦₆₄ u_568) ∗
       ((s.sp + 0x570#64) ↦₆₄ u_570) ∗
       ((s.sp + 0x578#64) ↦₆₄ u_578) ∗
       ((s.sp + 0x6a0#64) ↦₆₄ u_6a0) ∗
       ((s.sp + 0x6a8#64) ↦₆₄ u_6a8) ∗
       ((s.sp + 0x6b0#64) ↦₆₄ u_6b0) ∗
       ((s.sp + 0x6b8#64) ↦₆₄ u_6b8) ∗
       ((s.sp + 0x7e0#64) ↦₆₄ u_7e0) ∗
       ((s.sp + 0x7e8#64) ↦₆₄ u_7e8) ∗
       ((s.sp + 0x7f0#64) ↦₆₄ u_7f0) ∗
       ((s.sp + 0x7f8#64) ↦₆₄ u_7f8))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x7b8#64) ↦₆₄ ik4) ∗
          ((coroPtr + 0x7c0#64) ↦₆₄ ik5) ∗
          ((coroPtr + 0x7c8#64) ↦₆₄ ik6) ∗
          ((coroPtr + 0x7d0#64) ↦₆₄ ik7) ∗
          ((coroPtr + 0x398#64) ↦₆₄ spk0) ∗
          ((coroPtr + 0x3a0#64) ↦₆₄ spk1) ∗
          ((coroPtr + 0x3a8#64) ↦₆₄ spk2) ∗
          ((coroPtr + 0x3b0#64) ↦₆₄ spk3) ∗
          ((coroPtr + 0x3b8#64) ↦₆₄ spk4) ∗
          ((coroPtr + 0x3c0#64) ↦₆₄ spk5) ∗
          ((coroPtr + 0x3c8#64) ↦₆₄ spk6) ∗
          ((coroPtr + 0x3d0#64) ↦₆₄ spk7) ∗
          ((coroPtr + 0x4b0#64) ↦₆₄ opk0) ∗
          ((coroPtr + 0x4b8#64) ↦₆₄ opk1) ∗
          ((coroPtr + 0x4c0#64) ↦₆₄ opk2) ∗
          ((coroPtr + 0x4c8#64) ↦₆₄ opk3) ∗
          ((coroPtr + 0x4d0#64) ↦₆₄ opk4) ∗
          ((coroPtr + 0x4d8#64) ↦₆₄ opk5) ∗
          ((coroPtr + 0x4e0#64) ↦₆₄ opk6) ∗
          ((coroPtr + 0x4e8#64) ↦₆₄ opk7) ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
          ((coroPtr + 0x3d8#64) ↦₆₄ kyb0) ∗
          ((coroPtr + 0x3e0#64) ↦₆₄ kyb1) ∗
          ((coroPtr + 0x3e8#64) ↦₆₄ kyb2) ∗
          ((coroPtr + 0x3f0#64) ↦₆₄ kyb3) ∗
          ((msgPtr + 0xa8#64) ↦₆₄ ekA0) ∗
          ((msgPtr + 0xb0#64) ↦₆₄ ekA1) ∗
          ((msgPtr + 0xb8#64) ↦₆₄ ekA2) ∗
          ((msgPtr + 0xc0#64) ↦₆₄ ekA3) ∗
          ((msgPtr + 0xc8#64) ↦₆₄ ikA0) ∗
          ((msgPtr + 0xd0#64) ↦₆₄ ikA1) ∗
          ((msgPtr + 0xd8#64) ↦₆₄ ikA2) ∗
          ((msgPtr + 0xe0#64) ↦₆₄ ikA3) ∗
          ((s.sp + 0x950#64) ↦₆₄ ik4) ∗
          ((s.sp + 0x958#64) ↦₆₄ ik5) ∗
          ((s.sp + 0x960#64) ↦₆₄ ik6) ∗
          ((s.sp + 0x968#64) ↦₆₄ ik7) ∗
          ((s.sp + 0xa90#64) ↦₆₄ spk0) ∗
          ((s.sp + 0xa98#64) ↦₆₄ spk1) ∗
          ((s.sp + 0xaa0#64) ↦₆₄ spk2) ∗
          ((s.sp + 0xaa8#64) ↦₆₄ spk3) ∗
          ((s.sp + 0xab0#64) ↦₆₄ spk4) ∗
          ((s.sp + 0xab8#64) ↦₆₄ spk5) ∗
          ((s.sp + 0xac0#64) ↦₆₄ spk6) ∗
          ((s.sp + 0xac8#64) ↦₆₄ spk7) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ opk0) ∗
          ((s.sp + 0x3e8#64) ↦₆₄ opk1) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ opk2) ∗
          ((s.sp + 0x3f8#64) ↦₆₄ opk3) ∗
          ((s.sp + 0x400#64) ↦₆₄ opk4) ∗
          ((s.sp + 0x408#64) ↦₆₄ opk5) ∗
          ((s.sp + 0x410#64) ↦₆₄ opk6) ∗
          ((s.sp + 0x418#64) ↦₆₄ opk7) ∗
          ((s.sp + 0x420#64) ↦₈ opk_b64) ∗
          ((s.sp + 0x560#64) ↦₆₄ kyb0) ∗
          ((s.sp + 0x568#64) ↦₆₄ kyb1) ∗
          ((s.sp + 0x570#64) ↦₆₄ kyb2) ∗
          ((s.sp + 0x578#64) ↦₆₄ kyb3) ∗
          ((s.sp + 0x6a0#64) ↦₆₄ ikA0) ∗
          ((s.sp + 0x6a8#64) ↦₆₄ ikA1) ∗
          ((s.sp + 0x6b0#64) ↦₆₄ ikA2) ∗
          ((s.sp + 0x6b8#64) ↦₆₄ ikA3) ∗
          ((s.sp + 0x7e0#64) ↦₆₄ ekA0) ∗
          ((s.sp + 0x7e8#64) ↦₆₄ ekA1) ∗
          ((s.sp + 0x7f0#64) ↦₆₄ ekA2) ∗
          ((s.sp + 0x7f8#64) ↦₆₄ ekA3)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0x798#64 ∧
        s1.readReg64 .x1 = localAddrPtr ∧
        s1.readReg64 .x2 = msgPtr + 0xc8#64 ∧
        s1.readReg64 .x3 = remoteAddrPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = s.sp + 0x370#64 ∧
        s1.readReg64 .x23 = s.sp + 0x930#64 ∧
        s1.readReg64 .x24 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x11d0#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg5c3_wp_trap b C abs s
      coroPtr msgPtr localAddrPtr remoteAddrPtr
      ik4 ik5 ik6 ik7
      spk0 spk1 spk2 spk3 spk4 spk5 spk6 spk7
      opk0 opk1 opk2 opk3 opk4 opk5 opk6 opk7
      kyb0 kyb1 kyb2 kyb3
      ikA0 ikA1 ikA2 ikA3
      ekA0 ekA1 ekA2 ekA3
      u_950 u_958 u_960 u_968
      u_a90 u_a98 u_aa0 u_aa8 u_ab0 u_ab8 u_ac0 u_ac8
      u_3e0 u_3e8 u_3f0 u_3f8 u_400 u_408 u_410 u_418
      u_560 u_568 u_570 u_578
      u_6a0 u_6a8 u_6b0 u_6b8
      u_7e0 u_7e8 u_7f0 u_7f8
      opk_b64 u_420 b_4f1
      hpc hrun hsp_align hx0 hx1 hx2 hx3 hx8 hx9 hx10 hx19 hx22 hx23 hx24 hx28)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg5d_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr kyberPreKeyId64 sameAcctWord
    ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7
    spk0 spk1 spk2 spk3 spk4 spk5 spk6 spk7
    opk0 opk1 opk2 opk3 opk4 opk5 opk6 opk7
    kyb0 kyb1 kyb2 kyb3
    ikA0 ikA1 ikA2 ikA3
    ekA0 ekA1 ekA2 ekA3
    c_658 c_660 c_668 c_670 c_678 c_680 c_688 c_690
    c_698 c_6a0 c_6a8 c_6b0 c_6b8 c_6c0 c_6c8 c_6d0
    c_6d8 c_6e0 c_6e8 c_6f0
    c_6f8 c_700 c_708 c_710
    c_718 c_720 c_728 c_730 c_738
    c_740 c_748 c_750 c_758 c_760 c_768 c_770 c_778 : BitVec 64)
    (opk_b64 c_780 c_781 : BitVec 8)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x11d0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = sameAcctWord)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = kyberPreKeyId64)
    (hx22 : s.readReg64 .x22 = s.sp + 0x370#64)
    (hx23 : s.readReg64 .x23 = s.sp + 0x930#64)
    (hx24 : s.readReg64 .x24 = coroPtr + 0x398#64)
    (hx28 : s.readReg64 .x28 = s.sp + 0xa90#64) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "libsignal_protocol::ratchet::initialize_bob_session" - ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64)) s
      (((s.sp + 0x930#64) ↦₆₄ ik0) ∗
       ((s.sp + 0x938#64) ↦₆₄ ik1) ∗
       ((s.sp + 0x940#64) ↦₆₄ ik2) ∗
       ((s.sp + 0x948#64) ↦₆₄ ik3) ∗
       ((s.sp + 0x950#64) ↦₆₄ ik4) ∗
       ((s.sp + 0x958#64) ↦₆₄ ik5) ∗
       ((s.sp + 0x960#64) ↦₆₄ ik6) ∗
       ((s.sp + 0x968#64) ↦₆₄ ik7) ∗
       ((s.sp + 0xa90#64) ↦₆₄ spk0) ∗
       ((s.sp + 0xa98#64) ↦₆₄ spk1) ∗
       ((s.sp + 0xaa0#64) ↦₆₄ spk2) ∗
       ((s.sp + 0xaa8#64) ↦₆₄ spk3) ∗
       ((s.sp + 0xab0#64) ↦₆₄ spk4) ∗
       ((s.sp + 0xab8#64) ↦₆₄ spk5) ∗
       ((s.sp + 0xac0#64) ↦₆₄ spk6) ∗
       ((s.sp + 0xac8#64) ↦₆₄ spk7) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ opk0) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ opk1) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ opk2) ∗
       ((s.sp + 0x3f8#64) ↦₆₄ opk3) ∗
       ((s.sp + 0x400#64) ↦₆₄ opk4) ∗
       ((s.sp + 0x408#64) ↦₆₄ opk5) ∗
       ((s.sp + 0x410#64) ↦₆₄ opk6) ∗
       ((s.sp + 0x418#64) ↦₆₄ opk7) ∗
       ((s.sp + 0x420#64) ↦₈ opk_b64) ∗
       ((s.sp + 0x560#64) ↦₆₄ kyb0) ∗
       ((s.sp + 0x568#64) ↦₆₄ kyb1) ∗
       ((s.sp + 0x570#64) ↦₆₄ kyb2) ∗
       ((s.sp + 0x578#64) ↦₆₄ kyb3) ∗
       ((s.sp + 0x6a0#64) ↦₆₄ ikA0) ∗
       ((s.sp + 0x6a8#64) ↦₆₄ ikA1) ∗
       ((s.sp + 0x6b0#64) ↦₆₄ ikA2) ∗
       ((s.sp + 0x6b8#64) ↦₆₄ ikA3) ∗
       ((s.sp + 0x7e0#64) ↦₆₄ ekA0) ∗
       ((s.sp + 0x7e8#64) ↦₆₄ ekA1) ∗
       ((s.sp + 0x7f0#64) ↦₆₄ ekA2) ∗
       ((s.sp + 0x7f8#64) ↦₆₄ ekA3) ∗
       ((coroPtr + 0x658#64) ↦₆₄ c_658) ∗
       ((coroPtr + 0x660#64) ↦₆₄ c_660) ∗
       ((coroPtr + 0x668#64) ↦₆₄ c_668) ∗
       ((coroPtr + 0x670#64) ↦₆₄ c_670) ∗
       ((coroPtr + 0x678#64) ↦₆₄ c_678) ∗
       ((coroPtr + 0x680#64) ↦₆₄ c_680) ∗
       ((coroPtr + 0x688#64) ↦₆₄ c_688) ∗
       ((coroPtr + 0x690#64) ↦₆₄ c_690) ∗
       ((coroPtr + 0x698#64) ↦₆₄ c_698) ∗
       ((coroPtr + 0x6a0#64) ↦₆₄ c_6a0) ∗
       ((coroPtr + 0x6a8#64) ↦₆₄ c_6a8) ∗
       ((coroPtr + 0x6b0#64) ↦₆₄ c_6b0) ∗
       ((coroPtr + 0x6b8#64) ↦₆₄ c_6b8) ∗
       ((coroPtr + 0x6c0#64) ↦₆₄ c_6c0) ∗
       ((coroPtr + 0x6c8#64) ↦₆₄ c_6c8) ∗
       ((coroPtr + 0x6d0#64) ↦₆₄ c_6d0) ∗
       ((coroPtr + 0x6d8#64) ↦₆₄ c_6d8) ∗
       ((coroPtr + 0x6e0#64) ↦₆₄ c_6e0) ∗
       ((coroPtr + 0x6e8#64) ↦₆₄ c_6e8) ∗
       ((coroPtr + 0x6f0#64) ↦₆₄ c_6f0) ∗
       ((coroPtr + 0x6f8#64) ↦₆₄ c_6f8) ∗
       ((coroPtr + 0x700#64) ↦₆₄ c_700) ∗
       ((coroPtr + 0x708#64) ↦₆₄ c_708) ∗
       ((coroPtr + 0x710#64) ↦₆₄ c_710) ∗
       ((coroPtr + 0x718#64) ↦₆₄ c_718) ∗
       ((coroPtr + 0x720#64) ↦₆₄ c_720) ∗
       ((coroPtr + 0x728#64) ↦₆₄ c_728) ∗
       ((coroPtr + 0x730#64) ↦₆₄ c_730) ∗
       ((coroPtr + 0x738#64) ↦₆₄ c_738) ∗
       ((coroPtr + 0x740#64) ↦₆₄ c_740) ∗
       ((coroPtr + 0x748#64) ↦₆₄ c_748) ∗
       ((coroPtr + 0x750#64) ↦₆₄ c_750) ∗
       ((coroPtr + 0x758#64) ↦₆₄ c_758) ∗
       ((coroPtr + 0x760#64) ↦₆₄ c_760) ∗
       ((coroPtr + 0x768#64) ↦₆₄ c_768) ∗
       ((coroPtr + 0x770#64) ↦₆₄ c_770) ∗
       ((coroPtr + 0x778#64) ↦₆₄ c_778) ∗
       ((coroPtr + 0x780#64) ↦₈ c_780) ∗
       ((coroPtr + 0x781#64) ↦₈ c_781))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x930#64) ↦₆₄ ik0) ∗
          ((s.sp + 0x938#64) ↦₆₄ ik1) ∗
          ((s.sp + 0x940#64) ↦₆₄ ik2) ∗
          ((s.sp + 0x948#64) ↦₆₄ ik3) ∗
          ((s.sp + 0x950#64) ↦₆₄ ik4) ∗
          ((s.sp + 0x958#64) ↦₆₄ ik5) ∗
          ((s.sp + 0x960#64) ↦₆₄ ik6) ∗
          ((s.sp + 0x968#64) ↦₆₄ ik7) ∗
          ((s.sp + 0xa90#64) ↦₆₄ spk0) ∗
          ((s.sp + 0xa98#64) ↦₆₄ spk1) ∗
          ((s.sp + 0xaa0#64) ↦₆₄ spk2) ∗
          ((s.sp + 0xaa8#64) ↦₆₄ spk3) ∗
          ((s.sp + 0xab0#64) ↦₆₄ spk4) ∗
          ((s.sp + 0xab8#64) ↦₆₄ spk5) ∗
          ((s.sp + 0xac0#64) ↦₆₄ spk6) ∗
          ((s.sp + 0xac8#64) ↦₆₄ spk7) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ opk0) ∗
          ((s.sp + 0x3e8#64) ↦₆₄ opk1) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ opk2) ∗
          ((s.sp + 0x3f8#64) ↦₆₄ opk3) ∗
          ((s.sp + 0x400#64) ↦₆₄ opk4) ∗
          ((s.sp + 0x408#64) ↦₆₄ opk5) ∗
          ((s.sp + 0x410#64) ↦₆₄ opk6) ∗
          ((s.sp + 0x418#64) ↦₆₄ opk7) ∗
          ((s.sp + 0x420#64) ↦₈ opk_b64) ∗
          ((s.sp + 0x560#64) ↦₆₄ kyb0) ∗
          ((s.sp + 0x568#64) ↦₆₄ kyb1) ∗
          ((s.sp + 0x570#64) ↦₆₄ kyb2) ∗
          ((s.sp + 0x578#64) ↦₆₄ kyb3) ∗
          ((s.sp + 0x6a0#64) ↦₆₄ ikA0) ∗
          ((s.sp + 0x6a8#64) ↦₆₄ ikA1) ∗
          ((s.sp + 0x6b0#64) ↦₆₄ ikA2) ∗
          ((s.sp + 0x6b8#64) ↦₆₄ ikA3) ∗
          ((s.sp + 0x7e0#64) ↦₆₄ ekA0) ∗
          ((s.sp + 0x7e8#64) ↦₆₄ ekA1) ∗
          ((s.sp + 0x7f0#64) ↦₆₄ ekA2) ∗
          ((s.sp + 0x7f8#64) ↦₆₄ ekA3) ∗
          ((coroPtr + 0x658#64) ↦₆₄ ik0) ∗
          ((coroPtr + 0x660#64) ↦₆₄ ik1) ∗
          ((coroPtr + 0x668#64) ↦₆₄ ik2) ∗
          ((coroPtr + 0x670#64) ↦₆₄ ik3) ∗
          ((coroPtr + 0x678#64) ↦₆₄ ik4) ∗
          ((coroPtr + 0x680#64) ↦₆₄ ik5) ∗
          ((coroPtr + 0x688#64) ↦₆₄ ik6) ∗
          ((coroPtr + 0x690#64) ↦₆₄ ik7) ∗
          ((coroPtr + 0x698#64) ↦₆₄ spk0) ∗
          ((coroPtr + 0x6a0#64) ↦₆₄ spk1) ∗
          ((coroPtr + 0x6a8#64) ↦₆₄ spk2) ∗
          ((coroPtr + 0x6b0#64) ↦₆₄ spk3) ∗
          ((coroPtr + 0x6b8#64) ↦₆₄ spk4) ∗
          ((coroPtr + 0x6c0#64) ↦₆₄ spk5) ∗
          ((coroPtr + 0x6c8#64) ↦₆₄ spk6) ∗
          ((coroPtr + 0x6d0#64) ↦₆₄ spk7) ∗
          ((coroPtr + 0x6d8#64) ↦₆₄ ikA0) ∗
          ((coroPtr + 0x6e0#64) ↦₆₄ ikA1) ∗
          ((coroPtr + 0x6e8#64) ↦₆₄ ikA2) ∗
          ((coroPtr + 0x6f0#64) ↦₆₄ ikA3) ∗
          ((coroPtr + 0x6f8#64) ↦₆₄ ekA0) ∗
          ((coroPtr + 0x700#64) ↦₆₄ ekA1) ∗
          ((coroPtr + 0x708#64) ↦₆₄ ekA2) ∗
          ((coroPtr + 0x710#64) ↦₆₄ ekA3) ∗
          ((coroPtr + 0x718#64) ↦₆₄ kyb0) ∗
          ((coroPtr + 0x720#64) ↦₆₄ kyb1) ∗
          ((coroPtr + 0x728#64) ↦₆₄ kyb2) ∗
          ((coroPtr + 0x730#64) ↦₆₄ kyb3) ∗
          ((coroPtr + 0x738#64) ↦₆₄ kyberPreKeyId64) ∗
          ((coroPtr + 0x740#64) ↦₆₄ opk0) ∗
          ((coroPtr + 0x748#64) ↦₆₄ opk1) ∗
          ((coroPtr + 0x750#64) ↦₆₄ opk2) ∗
          ((coroPtr + 0x758#64) ↦₆₄ opk3) ∗
          ((coroPtr + 0x760#64) ↦₆₄ opk4) ∗
          ((coroPtr + 0x768#64) ↦₆₄ opk5) ∗
          ((coroPtr + 0x770#64) ↦₆₄ opk6) ∗
          ((coroPtr + 0x778#64) ↦₆₄ opk7) ∗
          ((coroPtr + 0x780#64) ↦₈ opk_b64) ∗
          ((coroPtr + 0x781#64) ↦₈ sameAcctWord.setWidth 8)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0x658#64 ∧
        s1.readReg64 .x1 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = kyberPreKeyId64 ∧
        s1.readReg64 .x22 = s.sp + 0x370#64 ∧
        s1.readReg64 .x23 = s.sp + 0x930#64 ∧
        s1.readReg64 .x24 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x125c#64) := by
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x11d0 0x1258
  dsimp only [trTrapProgAt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = sameAcctWord := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = kyberPreKeyId64 := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = s.sp + 0x370#64 := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = s.sp + 0x930#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = coroPtr + 0x398#64 := hx24
  have hx28' : s.readReg64 (Reg.gpr 28#5) = s.sp + 0xa90#64 := hx28
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P2.5d (`+0x11d0 → +0x1258`): populates `BobSignalProtocolParameters` at
`coroPtr + 0x658..0x781` and calls `initialize_bob_session`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg5d_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr kyberPreKeyId64 sameAcctWord
    ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7
    spk0 spk1 spk2 spk3 spk4 spk5 spk6 spk7
    opk0 opk1 opk2 opk3 opk4 opk5 opk6 opk7
    kyb0 kyb1 kyb2 kyb3
    ikA0 ikA1 ikA2 ikA3
    ekA0 ekA1 ekA2 ekA3
    c_658 c_660 c_668 c_670 c_678 c_680 c_688 c_690
    c_698 c_6a0 c_6a8 c_6b0 c_6b8 c_6c0 c_6c8 c_6d0
    c_6d8 c_6e0 c_6e8 c_6f0
    c_6f8 c_700 c_708 c_710
    c_718 c_720 c_728 c_730 c_738
    c_740 c_748 c_750 c_758 c_760 c_768 c_770 c_778 : BitVec 64)
    (opk_b64 c_780 c_781 : BitVec 8)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x11d0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = sameAcctWord)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = kyberPreKeyId64)
    (hx22 : s.readReg64 .x22 = s.sp + 0x370#64)
    (hx23 : s.readReg64 .x23 = s.sp + 0x930#64)
    (hx24 : s.readReg64 .x24 = coroPtr + 0x398#64)
    (hx28 : s.readReg64 .x28 = s.sp + 0xa90#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "libsignal_protocol::ratchet::initialize_bob_session" - ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64)) s
      (((s.sp + 0x930#64) ↦₆₄ ik0) ∗
       ((s.sp + 0x938#64) ↦₆₄ ik1) ∗
       ((s.sp + 0x940#64) ↦₆₄ ik2) ∗
       ((s.sp + 0x948#64) ↦₆₄ ik3) ∗
       ((s.sp + 0x950#64) ↦₆₄ ik4) ∗
       ((s.sp + 0x958#64) ↦₆₄ ik5) ∗
       ((s.sp + 0x960#64) ↦₆₄ ik6) ∗
       ((s.sp + 0x968#64) ↦₆₄ ik7) ∗
       ((s.sp + 0xa90#64) ↦₆₄ spk0) ∗
       ((s.sp + 0xa98#64) ↦₆₄ spk1) ∗
       ((s.sp + 0xaa0#64) ↦₆₄ spk2) ∗
       ((s.sp + 0xaa8#64) ↦₆₄ spk3) ∗
       ((s.sp + 0xab0#64) ↦₆₄ spk4) ∗
       ((s.sp + 0xab8#64) ↦₆₄ spk5) ∗
       ((s.sp + 0xac0#64) ↦₆₄ spk6) ∗
       ((s.sp + 0xac8#64) ↦₆₄ spk7) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ opk0) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ opk1) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ opk2) ∗
       ((s.sp + 0x3f8#64) ↦₆₄ opk3) ∗
       ((s.sp + 0x400#64) ↦₆₄ opk4) ∗
       ((s.sp + 0x408#64) ↦₆₄ opk5) ∗
       ((s.sp + 0x410#64) ↦₆₄ opk6) ∗
       ((s.sp + 0x418#64) ↦₆₄ opk7) ∗
       ((s.sp + 0x420#64) ↦₈ opk_b64) ∗
       ((s.sp + 0x560#64) ↦₆₄ kyb0) ∗
       ((s.sp + 0x568#64) ↦₆₄ kyb1) ∗
       ((s.sp + 0x570#64) ↦₆₄ kyb2) ∗
       ((s.sp + 0x578#64) ↦₆₄ kyb3) ∗
       ((s.sp + 0x6a0#64) ↦₆₄ ikA0) ∗
       ((s.sp + 0x6a8#64) ↦₆₄ ikA1) ∗
       ((s.sp + 0x6b0#64) ↦₆₄ ikA2) ∗
       ((s.sp + 0x6b8#64) ↦₆₄ ikA3) ∗
       ((s.sp + 0x7e0#64) ↦₆₄ ekA0) ∗
       ((s.sp + 0x7e8#64) ↦₆₄ ekA1) ∗
       ((s.sp + 0x7f0#64) ↦₆₄ ekA2) ∗
       ((s.sp + 0x7f8#64) ↦₆₄ ekA3) ∗
       ((coroPtr + 0x658#64) ↦₆₄ c_658) ∗
       ((coroPtr + 0x660#64) ↦₆₄ c_660) ∗
       ((coroPtr + 0x668#64) ↦₆₄ c_668) ∗
       ((coroPtr + 0x670#64) ↦₆₄ c_670) ∗
       ((coroPtr + 0x678#64) ↦₆₄ c_678) ∗
       ((coroPtr + 0x680#64) ↦₆₄ c_680) ∗
       ((coroPtr + 0x688#64) ↦₆₄ c_688) ∗
       ((coroPtr + 0x690#64) ↦₆₄ c_690) ∗
       ((coroPtr + 0x698#64) ↦₆₄ c_698) ∗
       ((coroPtr + 0x6a0#64) ↦₆₄ c_6a0) ∗
       ((coroPtr + 0x6a8#64) ↦₆₄ c_6a8) ∗
       ((coroPtr + 0x6b0#64) ↦₆₄ c_6b0) ∗
       ((coroPtr + 0x6b8#64) ↦₆₄ c_6b8) ∗
       ((coroPtr + 0x6c0#64) ↦₆₄ c_6c0) ∗
       ((coroPtr + 0x6c8#64) ↦₆₄ c_6c8) ∗
       ((coroPtr + 0x6d0#64) ↦₆₄ c_6d0) ∗
       ((coroPtr + 0x6d8#64) ↦₆₄ c_6d8) ∗
       ((coroPtr + 0x6e0#64) ↦₆₄ c_6e0) ∗
       ((coroPtr + 0x6e8#64) ↦₆₄ c_6e8) ∗
       ((coroPtr + 0x6f0#64) ↦₆₄ c_6f0) ∗
       ((coroPtr + 0x6f8#64) ↦₆₄ c_6f8) ∗
       ((coroPtr + 0x700#64) ↦₆₄ c_700) ∗
       ((coroPtr + 0x708#64) ↦₆₄ c_708) ∗
       ((coroPtr + 0x710#64) ↦₆₄ c_710) ∗
       ((coroPtr + 0x718#64) ↦₆₄ c_718) ∗
       ((coroPtr + 0x720#64) ↦₆₄ c_720) ∗
       ((coroPtr + 0x728#64) ↦₆₄ c_728) ∗
       ((coroPtr + 0x730#64) ↦₆₄ c_730) ∗
       ((coroPtr + 0x738#64) ↦₆₄ c_738) ∗
       ((coroPtr + 0x740#64) ↦₆₄ c_740) ∗
       ((coroPtr + 0x748#64) ↦₆₄ c_748) ∗
       ((coroPtr + 0x750#64) ↦₆₄ c_750) ∗
       ((coroPtr + 0x758#64) ↦₆₄ c_758) ∗
       ((coroPtr + 0x760#64) ↦₆₄ c_760) ∗
       ((coroPtr + 0x768#64) ↦₆₄ c_768) ∗
       ((coroPtr + 0x770#64) ↦₆₄ c_770) ∗
       ((coroPtr + 0x778#64) ↦₆₄ c_778) ∗
       ((coroPtr + 0x780#64) ↦₈ c_780) ∗
       ((coroPtr + 0x781#64) ↦₈ c_781))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x930#64) ↦₆₄ ik0) ∗
          ((s.sp + 0x938#64) ↦₆₄ ik1) ∗
          ((s.sp + 0x940#64) ↦₆₄ ik2) ∗
          ((s.sp + 0x948#64) ↦₆₄ ik3) ∗
          ((s.sp + 0x950#64) ↦₆₄ ik4) ∗
          ((s.sp + 0x958#64) ↦₆₄ ik5) ∗
          ((s.sp + 0x960#64) ↦₆₄ ik6) ∗
          ((s.sp + 0x968#64) ↦₆₄ ik7) ∗
          ((s.sp + 0xa90#64) ↦₆₄ spk0) ∗
          ((s.sp + 0xa98#64) ↦₆₄ spk1) ∗
          ((s.sp + 0xaa0#64) ↦₆₄ spk2) ∗
          ((s.sp + 0xaa8#64) ↦₆₄ spk3) ∗
          ((s.sp + 0xab0#64) ↦₆₄ spk4) ∗
          ((s.sp + 0xab8#64) ↦₆₄ spk5) ∗
          ((s.sp + 0xac0#64) ↦₆₄ spk6) ∗
          ((s.sp + 0xac8#64) ↦₆₄ spk7) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ opk0) ∗
          ((s.sp + 0x3e8#64) ↦₆₄ opk1) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ opk2) ∗
          ((s.sp + 0x3f8#64) ↦₆₄ opk3) ∗
          ((s.sp + 0x400#64) ↦₆₄ opk4) ∗
          ((s.sp + 0x408#64) ↦₆₄ opk5) ∗
          ((s.sp + 0x410#64) ↦₆₄ opk6) ∗
          ((s.sp + 0x418#64) ↦₆₄ opk7) ∗
          ((s.sp + 0x420#64) ↦₈ opk_b64) ∗
          ((s.sp + 0x560#64) ↦₆₄ kyb0) ∗
          ((s.sp + 0x568#64) ↦₆₄ kyb1) ∗
          ((s.sp + 0x570#64) ↦₆₄ kyb2) ∗
          ((s.sp + 0x578#64) ↦₆₄ kyb3) ∗
          ((s.sp + 0x6a0#64) ↦₆₄ ikA0) ∗
          ((s.sp + 0x6a8#64) ↦₆₄ ikA1) ∗
          ((s.sp + 0x6b0#64) ↦₆₄ ikA2) ∗
          ((s.sp + 0x6b8#64) ↦₆₄ ikA3) ∗
          ((s.sp + 0x7e0#64) ↦₆₄ ekA0) ∗
          ((s.sp + 0x7e8#64) ↦₆₄ ekA1) ∗
          ((s.sp + 0x7f0#64) ↦₆₄ ekA2) ∗
          ((s.sp + 0x7f8#64) ↦₆₄ ekA3) ∗
          ((coroPtr + 0x658#64) ↦₆₄ ik0) ∗
          ((coroPtr + 0x660#64) ↦₆₄ ik1) ∗
          ((coroPtr + 0x668#64) ↦₆₄ ik2) ∗
          ((coroPtr + 0x670#64) ↦₆₄ ik3) ∗
          ((coroPtr + 0x678#64) ↦₆₄ ik4) ∗
          ((coroPtr + 0x680#64) ↦₆₄ ik5) ∗
          ((coroPtr + 0x688#64) ↦₆₄ ik6) ∗
          ((coroPtr + 0x690#64) ↦₆₄ ik7) ∗
          ((coroPtr + 0x698#64) ↦₆₄ spk0) ∗
          ((coroPtr + 0x6a0#64) ↦₆₄ spk1) ∗
          ((coroPtr + 0x6a8#64) ↦₆₄ spk2) ∗
          ((coroPtr + 0x6b0#64) ↦₆₄ spk3) ∗
          ((coroPtr + 0x6b8#64) ↦₆₄ spk4) ∗
          ((coroPtr + 0x6c0#64) ↦₆₄ spk5) ∗
          ((coroPtr + 0x6c8#64) ↦₆₄ spk6) ∗
          ((coroPtr + 0x6d0#64) ↦₆₄ spk7) ∗
          ((coroPtr + 0x6d8#64) ↦₆₄ ikA0) ∗
          ((coroPtr + 0x6e0#64) ↦₆₄ ikA1) ∗
          ((coroPtr + 0x6e8#64) ↦₆₄ ikA2) ∗
          ((coroPtr + 0x6f0#64) ↦₆₄ ikA3) ∗
          ((coroPtr + 0x6f8#64) ↦₆₄ ekA0) ∗
          ((coroPtr + 0x700#64) ↦₆₄ ekA1) ∗
          ((coroPtr + 0x708#64) ↦₆₄ ekA2) ∗
          ((coroPtr + 0x710#64) ↦₆₄ ekA3) ∗
          ((coroPtr + 0x718#64) ↦₆₄ kyb0) ∗
          ((coroPtr + 0x720#64) ↦₆₄ kyb1) ∗
          ((coroPtr + 0x728#64) ↦₆₄ kyb2) ∗
          ((coroPtr + 0x730#64) ↦₆₄ kyb3) ∗
          ((coroPtr + 0x738#64) ↦₆₄ kyberPreKeyId64) ∗
          ((coroPtr + 0x740#64) ↦₆₄ opk0) ∗
          ((coroPtr + 0x748#64) ↦₆₄ opk1) ∗
          ((coroPtr + 0x750#64) ↦₆₄ opk2) ∗
          ((coroPtr + 0x758#64) ↦₆₄ opk3) ∗
          ((coroPtr + 0x760#64) ↦₆₄ opk4) ∗
          ((coroPtr + 0x768#64) ↦₆₄ opk5) ∗
          ((coroPtr + 0x770#64) ↦₆₄ opk6) ∗
          ((coroPtr + 0x778#64) ↦₆₄ opk7) ∗
          ((coroPtr + 0x780#64) ↦₈ opk_b64) ∗
          ((coroPtr + 0x781#64) ↦₈ sameAcctWord.setWidth 8)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0x658#64 ∧
        s1.readReg64 .x1 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = kyberPreKeyId64 ∧
        s1.readReg64 .x22 = s.sp + 0x370#64 ∧
        s1.readReg64 .x23 = s.sp + 0x930#64 ∧
        s1.readReg64 .x24 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x125c#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg5d_wp_trap b C abs s
      coroPtr kyberPreKeyId64 sameAcctWord
      ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7
      spk0 spk1 spk2 spk3 spk4 spk5 spk6 spk7
      opk0 opk1 opk2 opk3 opk4 opk5 opk6 opk7
      kyb0 kyb1 kyb2 kyb3
      ikA0 ikA1 ikA2 ikA3
      ekA0 ekA1 ekA2 ekA3
      c_658 c_660 c_668 c_670 c_678 c_680 c_688 c_690
      c_698 c_6a0 c_6a8 c_6b0 c_6b8 c_6c0 c_6c8 c_6d0
      c_6d8 c_6e0 c_6e8 c_6f0
      c_6f8 c_700 c_708 c_710
      c_718 c_720 c_728 c_730 c_738
      c_740 c_748 c_750 c_758 c_760 c_768 c_770 c_778
      opk_b64 c_780 c_781
      hpc hrun hsp_align hx0 hx19 hx21 hx22 hx23 hx24 hx28)

/-! ## 2. Stage P2.6 Segment Proofs (`+0x125c → +0x1778`) -/

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg6a_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr idStorePtr idStoreVt getLocalRegIdShimAddr
    ss0 ss1 ss2 ss3 ss4 ss5 ss6
    u_4f8 u_500 u_508 u_510 u_518 u_520 u_528 u_650 : BitVec 64)
    (ssRest : List (BitVec 8))
    (hss0_ne : ss0 + 1#64 ≠ 0#64)
    (hssRest_len : ssRest.length = 288)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x125c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (trTrapProgAt b C abs) getLocalRegIdShimAddr s
      (((s.sp + 0x3e0#64) ↦₆₄ ss0) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ ss1) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ ss2) ∗
       ((s.sp + 0x3f8#64) ↦₆₄ ss3) ∗
       ((s.sp + 0x400#64) ↦₆₄ ss4) ∗
       ((s.sp + 0x408#64) ↦₆₄ ss5) ∗
       ((s.sp + 0x410#64) ↦₆₄ ss6) ∗
       ((s.sp + 0x418#64) ↦ₛ ssRest) ∗
       memRegion (s.sp + 0xa90#64) 288 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗
       ((coroPtr + 0x500#64) ↦₆₄ u_500) ∗
       ((coroPtr + 0x508#64) ↦₆₄ u_508) ∗
       ((coroPtr + 0x510#64) ↦₆₄ u_510) ∗
       ((coroPtr + 0x518#64) ↦₆₄ u_518) ∗
       ((coroPtr + 0x520#64) ↦₆₄ u_520) ∗
       ((coroPtr + 0x528#64) ↦₆₄ u_528) ∗
       memRegion (coroPtr + 0x530#64) 288 ∗
       ((coroPtr + 0x650#64) ↦₆₄ u_650) ∗
       ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
       ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
       ((idStoreVt + 0x20#64) ↦₆₄ᵣ getLocalRegIdShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e0#64) ↦₆₄ ss0) ∗
          ((s.sp + 0x3e8#64) ↦₆₄ ss1) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ ss2) ∗
          ((s.sp + 0x3f8#64) ↦₆₄ ss3) ∗
          ((s.sp + 0x400#64) ↦₆₄ ss4) ∗
          ((s.sp + 0x408#64) ↦₆₄ ss5) ∗
          ((s.sp + 0x410#64) ↦₆₄ ss6) ∗
          ((s.sp + 0x418#64) ↦ₛ ssRest) ∗
          ((s.sp + 0xa90#64) ↦ₛ ssRest) ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ ss0) ∗
          ((coroPtr + 0x500#64) ↦₆₄ ss1) ∗
          ((coroPtr + 0x508#64) ↦₆₄ ss2) ∗
          ((coroPtr + 0x510#64) ↦₆₄ ss3) ∗
          ((coroPtr + 0x518#64) ↦₆₄ ss4) ∗
          ((coroPtr + 0x520#64) ↦₆₄ ss5) ∗
          ((coroPtr + 0x528#64) ↦₆₄ ss6) ∗
          ((coroPtr + 0x530#64) ↦ₛ ssRest) ∗
          ((coroPtr + 0x650#64) ↦₆₄ (coroPtr + 0x4f8#64)) ∗
          ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
          ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
          ((idStoreVt + 0x20#64) ↦₆₄ᵣ getLocalRegIdShimAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = idStorePtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = ss1 ∧
        s1.readReg64 .x21 = ss0 ∧
        s1.readReg64 .x22 = ss4 ∧
        s1.readReg64 .x23 = ss2 ∧
        s1.readReg64 .x24 = ss3 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = ss5 ∧
        s1.readReg64 .x27 = ss6 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x12d8#64) := by
  have hmemcpy := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_memcpy_ok_trap (b := b) (C := C) (abs := abs)
  have hss0_beq : (ss0 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hss0_ne
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x125c 0x12d4
  dsimp only [trTrapProgAt] at hmemcpy hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  wp_call hmemcpy (s.sp + 0xa90#64, s.sp + 0x418#64, ssRest)
  wp_steps
  wp_call hmemcpy (coroPtr + 0x530#64, s.sp + 0xa90#64, ssRest)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- Segment P2.6a (`+0x125c → +0x12d4`): copies the 344-byte `SessionState` into
`coroPtr + 0x4f8..0x650` and invokes `get_local_registration_id` (`blr x8`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg6a_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr idStorePtr idStoreVt getLocalRegIdShimAddr
    ss0 ss1 ss2 ss3 ss4 ss5 ss6
    u_4f8 u_500 u_508 u_510 u_518 u_520 u_528 u_650 : BitVec 64)
    (ssRest : List (BitVec 8))
    (hss0_ne : ss0 + 1#64 ≠ 0#64)
    (hssRest_len : ssRest.length = 288)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x125c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs) getLocalRegIdShimAddr s
      (((s.sp + 0x3e0#64) ↦₆₄ ss0) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ ss1) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ ss2) ∗
       ((s.sp + 0x3f8#64) ↦₆₄ ss3) ∗
       ((s.sp + 0x400#64) ↦₆₄ ss4) ∗
       ((s.sp + 0x408#64) ↦₆₄ ss5) ∗
       ((s.sp + 0x410#64) ↦₆₄ ss6) ∗
       ((s.sp + 0x418#64) ↦ₛ ssRest) ∗
       memRegion (s.sp + 0xa90#64) 288 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗
       ((coroPtr + 0x500#64) ↦₆₄ u_500) ∗
       ((coroPtr + 0x508#64) ↦₆₄ u_508) ∗
       ((coroPtr + 0x510#64) ↦₆₄ u_510) ∗
       ((coroPtr + 0x518#64) ↦₆₄ u_518) ∗
       ((coroPtr + 0x520#64) ↦₆₄ u_520) ∗
       ((coroPtr + 0x528#64) ↦₆₄ u_528) ∗
       memRegion (coroPtr + 0x530#64) 288 ∗
       ((coroPtr + 0x650#64) ↦₆₄ u_650) ∗
       ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
       ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
       ((idStoreVt + 0x20#64) ↦₆₄ᵣ getLocalRegIdShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e0#64) ↦₆₄ ss0) ∗
          ((s.sp + 0x3e8#64) ↦₆₄ ss1) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ ss2) ∗
          ((s.sp + 0x3f8#64) ↦₆₄ ss3) ∗
          ((s.sp + 0x400#64) ↦₆₄ ss4) ∗
          ((s.sp + 0x408#64) ↦₆₄ ss5) ∗
          ((s.sp + 0x410#64) ↦₆₄ ss6) ∗
          ((s.sp + 0x418#64) ↦ₛ ssRest) ∗
          ((s.sp + 0xa90#64) ↦ₛ ssRest) ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ ss0) ∗
          ((coroPtr + 0x500#64) ↦₆₄ ss1) ∗
          ((coroPtr + 0x508#64) ↦₆₄ ss2) ∗
          ((coroPtr + 0x510#64) ↦₆₄ ss3) ∗
          ((coroPtr + 0x518#64) ↦₆₄ ss4) ∗
          ((coroPtr + 0x520#64) ↦₆₄ ss5) ∗
          ((coroPtr + 0x528#64) ↦₆₄ ss6) ∗
          ((coroPtr + 0x530#64) ↦ₛ ssRest) ∗
          ((coroPtr + 0x650#64) ↦₆₄ (coroPtr + 0x4f8#64)) ∗
          ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
          ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
          ((idStoreVt + 0x20#64) ↦₆₄ᵣ getLocalRegIdShimAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = idStorePtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = ss1 ∧
        s1.readReg64 .x21 = ss0 ∧
        s1.readReg64 .x22 = ss4 ∧
        s1.readReg64 .x23 = ss2 ∧
        s1.readReg64 .x24 = ss3 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = ss5 ∧
        s1.readReg64 .x27 = ss6 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x12d8#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg6a_wp_trap b C abs s
      coroPtr idStorePtr idStoreVt getLocalRegIdShimAddr
      ss0 ss1 ss2 ss3 ss4 ss5 ss6
      u_4f8 u_500 u_508 u_510 u_518 u_520 u_528 u_650
      ssRest hss0_ne hssRest_len hpc hrun hsp_align hx19)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg6b_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr ctxPtr regIdFutPtr regIdFutVt localRegIdPollAddr
    v_98 v_a0 v_b0 u_788 u_790 : BitVec 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x12d8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = regIdFutPtr)
    (hx1 : s.readReg64 .x1 = regIdFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (trTrapProgAt b C abs) localRegIdPollAddr s
      (((s.sp + 0x98#64) ↦₆₄ v_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((coroPtr + 0x788#64) ↦₆₄ u_788) ∗
       ((coroPtr + 0x790#64) ↦₆₄ u_790) ∗
       ((regIdFutVt + 0x18#64) ↦₆₄ᵣ localRegIdPollAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
          ((coroPtr + 0x790#64) ↦₆₄ regIdFutVt) ∗
          ((regIdFutVt + 0x18#64) ↦₆₄ᵣ localRegIdPollAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = regIdFutPtr ∧
        s1.readReg64 .x1 = ctxPtr ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = v_b0 ∧
        s1.readReg64 .x23 = v_a0 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_98 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x9f4#64) := by
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x12d8 0x12ec
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x9e0 0x9f0
  dsimp only [trTrapProgAt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = regIdFutPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = regIdFutVt := hx1
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P2.6b (`+0x12d8 → +0x09f0`): stores `(regIdFutPtr, regIdFutVt)` at
`coroPtr + 0x788..0x790` and polls `get_local_registration_id` (`blr x9`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg6b_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr ctxPtr regIdFutPtr regIdFutVt localRegIdPollAddr
    v_98 v_a0 v_b0 u_788 u_790 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x12d8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = regIdFutPtr)
    (hx1 : s.readReg64 .x1 = regIdFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs) localRegIdPollAddr s
      (((s.sp + 0x98#64) ↦₆₄ v_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((coroPtr + 0x788#64) ↦₆₄ u_788) ∗
       ((coroPtr + 0x790#64) ↦₆₄ u_790) ∗
       ((regIdFutVt + 0x18#64) ↦₆₄ᵣ localRegIdPollAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
          ((coroPtr + 0x790#64) ↦₆₄ regIdFutVt) ∗
          ((regIdFutVt + 0x18#64) ↦₆₄ᵣ localRegIdPollAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = regIdFutPtr ∧
        s1.readReg64 .x1 = ctxPtr ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = v_b0 ∧
        s1.readReg64 .x23 = v_a0 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_98 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x9f4#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg6b_wp_trap b C abs s
      coroPtr ctxPtr regIdFutPtr regIdFutVt localRegIdPollAddr
      v_98 v_a0 v_b0 u_788 u_790 hpc hrun hsp_align hx0 hx1 hx19)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg6c_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr regIdFutPtr regIdFutVt localRegIdDropAddr
    v_98 v_a0 v_b0 u_88 u_98 u_a0 u_a8 u_b0 u_b8 u_d0
    u_3f0 u_3f8 u_400 u_408 : BitVec 64)
    (localRegId u_3ec : BitVec 32)
    (hdrop_nz : localRegIdDropAddr ≠ 0#64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x9f4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = v_a0)
    (hx26 : s.readReg64 .x26 = v_98) :
    SepWP (trTrapProgAt b C abs) localRegIdDropAddr s
      (((s.sp + 0x3e0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
       ((s.sp + 0x3e8#64) ↦₃₂ localRegId) ∗
       ((s.sp + 0x3ec#64) ↦₃₂ u_3ec) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ u_3f0) ∗
       ((s.sp + 0x3f8#64) ↦₆₄ u_3f8) ∗
       ((s.sp + 0x400#64) ↦₆₄ u_400) ∗
       ((s.sp + 0x408#64) ↦₆₄ u_408) ∗
       ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
       ((coroPtr + 0x790#64) ↦₆₄ regIdFutVt) ∗
       ((regIdFutVt + 0x0#64) ↦₆₄ᵣ localRegIdDropAddr) ∗
       ((s.sp + 0x88#64) ↦₆₄ u_88) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((s.sp + 0x3e8#64) ↦₃₂ localRegId) ∗
          ((s.sp + 0x3ec#64) ↦₃₂ u_3ec) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ u_3f0) ∗
          ((s.sp + 0x3f8#64) ↦₆₄ u_3f8) ∗
          ((s.sp + 0x400#64) ↦₆₄ u_400) ∗
          ((s.sp + 0x408#64) ↦₆₄ u_408) ∗
          ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
          ((coroPtr + 0x790#64) ↦₆₄ regIdFutVt) ∗
          ((regIdFutVt + 0x0#64) ↦₆₄ᵣ localRegIdDropAddr) ∗
          ((s.sp + 0x88#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xa8#64) ↦₆₄ u_400) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ u_3f0) ∗
          ((s.sp + 0xd0#64) ↦₆₄ u_3f8)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = regIdFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = regIdFutPtr ∧
        s1.readReg64 .x22 = u_3ec.zeroExtend 64 ∧
        s1.readReg64 .x23 = localRegId.zeroExtend 64 ∧
        s1.readReg64 .x24 = regIdFutVt ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_98 ∧
        s1.readReg64 .x27 = u_408 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xb3c#64) := by
  have hdrop_beq : (localRegIdDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x9f4 0x9fc
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xaf8 0xb38
  dsimp only [trTrapProgAt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = v_b0 := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = v_a0 := hx23
  have hx26' : s.readReg64 (Reg.gpr 26#5) = v_98 := hx26
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P2.6c (`+0x09f4 → +0x0b38`): reads `Poll::Ready(Ok(localRegId))`, spills registers, and
invokes `localRegIdDropAddr` (`blr x8`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg6c_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr regIdFutPtr regIdFutVt localRegIdDropAddr
    v_98 v_a0 v_b0 u_88 u_98 u_a0 u_a8 u_b0 u_b8 u_d0
    u_3f0 u_3f8 u_400 u_408 : BitVec 64)
    (localRegId u_3ec : BitVec 32)
    (hdrop_nz : localRegIdDropAddr ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x9f4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = v_a0)
    (hx26 : s.readReg64 .x26 = v_98) :
    SepWP (tripleRatchetProgAt b C ctl abs) localRegIdDropAddr s
      (((s.sp + 0x3e0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
       ((s.sp + 0x3e8#64) ↦₃₂ localRegId) ∗
       ((s.sp + 0x3ec#64) ↦₃₂ u_3ec) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ u_3f0) ∗
       ((s.sp + 0x3f8#64) ↦₆₄ u_3f8) ∗
       ((s.sp + 0x400#64) ↦₆₄ u_400) ∗
       ((s.sp + 0x408#64) ↦₆₄ u_408) ∗
       ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
       ((coroPtr + 0x790#64) ↦₆₄ regIdFutVt) ∗
       ((regIdFutVt + 0x0#64) ↦₆₄ᵣ localRegIdDropAddr) ∗
       ((s.sp + 0x88#64) ↦₆₄ u_88) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((s.sp + 0x3e8#64) ↦₃₂ localRegId) ∗
          ((s.sp + 0x3ec#64) ↦₃₂ u_3ec) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ u_3f0) ∗
          ((s.sp + 0x3f8#64) ↦₆₄ u_3f8) ∗
          ((s.sp + 0x400#64) ↦₆₄ u_400) ∗
          ((s.sp + 0x408#64) ↦₆₄ u_408) ∗
          ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
          ((coroPtr + 0x790#64) ↦₆₄ regIdFutVt) ∗
          ((regIdFutVt + 0x0#64) ↦₆₄ᵣ localRegIdDropAddr) ∗
          ((s.sp + 0x88#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xa8#64) ↦₆₄ u_400) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ u_3f0) ∗
          ((s.sp + 0xd0#64) ↦₆₄ u_3f8)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = regIdFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = regIdFutPtr ∧
        s1.readReg64 .x22 = u_3ec.zeroExtend 64 ∧
        s1.readReg64 .x23 = localRegId.zeroExtend 64 ∧
        s1.readReg64 .x24 = regIdFutVt ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_98 ∧
        s1.readReg64 .x27 = u_408 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xb3c#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg6c_wp_trap b C abs s
      coroPtr regIdFutPtr regIdFutVt localRegIdDropAddr
      v_98 v_a0 v_b0 u_88 u_98 u_a0 u_a8 u_b0 u_b8 u_d0
      u_3f0 u_3f8 u_400 u_408 localRegId u_3ec
      hdrop_nz hpc hrun hsp_align hx19 hx21 hx23 hx26)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg6d1_wp_trap {A : RustAlloc} (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr msgPtr regIdFutPtr regIdFutVt : BitVec 64)
    (localRegId remoteRegId u_648 u_64c : BitVec 32)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xb3c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = regIdFutPtr)
    (hx23 : s.readReg64 .x23 = localRegId.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = regIdFutVt) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xb80#64) s
      (((regIdFutVt + 0x8#64) ↦₆₄ᵣ 16#64) ∗
       ((regIdFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live regIdFutPtr 16 8 ∗
       memRegion regIdFutPtr 16 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((s.sp + 0x88#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((coroPtr + 0x648#64) ↦₃₂ u_648) ∗
       ((coroPtr + 0x64c#64) ↦₃₂ u_64c) ∗
       ((coroPtr + 0x650#64) ↦₆₄ (coroPtr + 0x4f8#64)) ∗
       ((msgPtr + 0xe8#64) ↦₃₂ remoteRegId))
      (fun s1 P_f =>
        (P_f ⊢
          ((regIdFutVt + 0x8#64) ↦₆₄ᵣ 16#64) ∗
          ((regIdFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((s.sp + 0x88#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          ((coroPtr + 0x648#64) ↦₃₂ remoteRegId) ∗
          ((coroPtr + 0x64c#64) ↦₃₂ localRegId) ∗
          ((coroPtr + 0x650#64) ↦₆₄ (coroPtr + 0x4f8#64)) ∗
          ((msgPtr + 0xe8#64) ↦₃₂ remoteRegId)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x1 = coroPtr + 0x4f8#64 ∧
        s1.readReg64 .x2 = 344#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = localRegId.zeroExtend 64 ∧
        s1.readReg64 .x24 = regIdFutVt ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  have hdealloc := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_dealloc_ok_trap (b := b) (C := C)
    (abs := abs) hA
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xb3c 0xb7c
  dsimp only [trTrapProgAt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = regIdFutPtr := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = localRegId.zeroExtend 64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = regIdFutVt := hx24
  wp_steps
  wp_call hdealloc (regIdFutPtr, 16, 8)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- Segment P2.6d1 (`+0x0b3c → +0x0b80`): deallocates `regIdFutPtr`, writes `localRegId` and
`remoteRegId` into `SessionState`, and prepares arguments for `promote_state`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg6d1_wp {A : RustAlloc} (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr msgPtr regIdFutPtr regIdFutVt : BitVec 64)
    (localRegId remoteRegId u_648 u_64c : BitVec 32)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xb3c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = regIdFutPtr)
    (hx23 : s.readReg64 .x23 = localRegId.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = regIdFutVt) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xb80#64) s
      (((regIdFutVt + 0x8#64) ↦₆₄ᵣ 16#64) ∗
       ((regIdFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live regIdFutPtr 16 8 ∗
       memRegion regIdFutPtr 16 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((s.sp + 0x88#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((coroPtr + 0x648#64) ↦₃₂ u_648) ∗
       ((coroPtr + 0x64c#64) ↦₃₂ u_64c) ∗
       ((coroPtr + 0x650#64) ↦₆₄ (coroPtr + 0x4f8#64)) ∗
       ((msgPtr + 0xe8#64) ↦₃₂ remoteRegId))
      (fun s1 P_f =>
        (P_f ⊢
          ((regIdFutVt + 0x8#64) ↦₆₄ᵣ 16#64) ∗
          ((regIdFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((s.sp + 0x88#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          ((coroPtr + 0x648#64) ↦₃₂ remoteRegId) ∗
          ((coroPtr + 0x64c#64) ↦₃₂ localRegId) ∗
          ((coroPtr + 0x650#64) ↦₆₄ (coroPtr + 0x4f8#64)) ∗
          ((msgPtr + 0xe8#64) ↦₃₂ remoteRegId)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x1 = coroPtr + 0x4f8#64 ∧
        s1.readReg64 .x2 = 344#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = localRegId.zeroExtend 64 ∧
        s1.readReg64 .x24 = regIdFutVt ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg6d1_wp_trap b C abs hA s
      coroPtr msgPtr regIdFutPtr regIdFutVt localRegId remoteRegId u_648 u_64c
      hpc hrun hsp_align hx19 hx21 hx23 hx24)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg6d2_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr : BitVec 64) (ssBytes : List (BitVec 8))
    (hss_len : ssBytes.length = 344)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xb80#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = s.sp + 0x3e0#64)
    (hx1 : s.readReg64 .x1 = coroPtr + 0x4f8#64)
    (hx2 : s.readReg64 .x2 = 344#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = coroPtr + 0xe0#64) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_state" - ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64)) s
      (((coroPtr + 0x4f8#64) ↦ₛ ssBytes) ∗
       memRegion (s.sp + 0x3e0#64) 344)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x4f8#64) ↦ₛ ssBytes) ∗
          ((s.sp + 0x3e0#64) ↦ₛ ssBytes)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x1 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xb90#64) := by
  have hmemcpy := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_memcpy_ok_trap (b := b) (C := C) (abs := abs)
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xb80 0xb8c
  dsimp only [trTrapProgAt] at hmemcpy hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = s.sp + 0x3e0#64 := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = coroPtr + 0x4f8#64 := hx1
  have hx2' : s.readReg64 (Reg.gpr 2#5) = 344#64 := hx2
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = coroPtr + 0xe0#64 := hx21
  wp_steps
  wp_call hmemcpy (s.sp + 0x3e0#64, coroPtr + 0x4f8#64, ssBytes)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- Segment P2.6d2 (`+0x0b80 → +0x0b8c`): copies the 344-byte `SessionState` to `sp + 0x3e0..0x538`
and calls `SessionRecord::promote_state`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg6d2_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr : BitVec 64) (ssBytes : List (BitVec 8))
    (hss_len : ssBytes.length = 344)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xb80#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = s.sp + 0x3e0#64)
    (hx1 : s.readReg64 .x1 = coroPtr + 0x4f8#64)
    (hx2 : s.readReg64 .x2 = 344#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = coroPtr + 0xe0#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_state" - ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64)) s
      (((coroPtr + 0x4f8#64) ↦ₛ ssBytes) ∗
       memRegion (s.sp + 0x3e0#64) 344)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x4f8#64) ↦ₛ ssBytes) ∗
          ((s.sp + 0x3e0#64) ↦ₛ ssBytes)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x1 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xb90#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg6d2_wp_trap b C abs s coroPtr ssBytes
      hss_len hpc hrun hsp_align hx0 hx1 hx2 hx19 hx21)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg6e_wp_trap {A : RustAlloc} (b : BitVec 64) (C : Crypto)
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
       ((coroPtr + 0x720#64) ↦₆₄ 1569#64) ∗
       ((coroPtr + 0x728#64) ↦₆₄ kyberKpSecPtr) ∗
       ((coroPtr + 0x730#64) ↦₆₄ 3169#64) ∗
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
       A.live kyberKpPubPtr 1569 1 ∗ memRegion kyberKpPubPtr 1569 ∗
       A.live kyberKpSecPtr 3169 1 ∗ memRegion kyberKpSecPtr 3169 ∗
       A.pool ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗
          ((coroPtr + 0x720#64) ↦₆₄ 1569#64) ∗
          ((coroPtr + 0x728#64) ↦₆₄ kyberKpSecPtr) ∗
          ((coroPtr + 0x730#64) ↦₆₄ 3169#64) ∗
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
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1698#64) := by
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
  wp_call hdealloc (kyberKpPubPtr, 1569, 1)
  wp_steps
  wp_call hdealloc (kyberKpSecPtr, 3169, 1)
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

/-- Segment P2.6e (`+0x0b90 → +0x1694`): reads prekey IDs from `msgPtr`, deallocates Kyber key
buffers, and calls `drop_glue::<process_prekey_impl>`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg6e_wp {A : RustAlloc} (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
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
       ((coroPtr + 0x720#64) ↦₆₄ 1569#64) ∗
       ((coroPtr + 0x728#64) ↦₆₄ kyberKpSecPtr) ∗
       ((coroPtr + 0x730#64) ↦₆₄ 3169#64) ∗
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
       A.live kyberKpPubPtr 1569 1 ∗ memRegion kyberKpPubPtr 1569 ∗
       A.live kyberKpSecPtr 3169 1 ∗ memRegion kyberKpSecPtr 3169 ∗
       A.pool ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗
          ((coroPtr + 0x720#64) ↦₆₄ 1569#64) ∗
          ((coroPtr + 0x728#64) ↦₆₄ kyberKpSecPtr) ∗
          ((coroPtr + 0x730#64) ↦₆₄ 3169#64) ∗
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
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1698#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg6e_wp_trap b C abs hA s
      coroPtr msgPtr kyberCtCap kyberKpPubPtr kyberKpSecPtr v_c8 u_a8 u_d0
      opkIdIsSome opkId kyberPreKeyId signedPreKeyId b_4f1 b_4f2
      hkyber_nz hpc hrun hsp_align hx19)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg6f_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr msgPtr remoteAddrPtr localAddrPtr
    opkPacked kyberPacked ss0 v_330 v_388
    u_250 u_258 u_260 u_270 u_278 u_298 u_2a0
    u_80 u_88 u_90 u_a0 u_a8 u_b0
    u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
    (opkIdIsSome signedPreKeyId u_268 u_26c u_2a8 u_b8 : BitVec 32)
    (msgVerByte b_390 b_3ac : BitVec 8)
    (hss0_ne : ss0 + 1#64 ≠ 0#64)
    (hpack_lo : (opkPacked &&& 0xff#64) = (opkIdIsSome.zeroExtend 64 &&& 0xff#64))
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1698#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = 0xfffffffffffffffe#64)
    (hx22 : s.readReg64 .x22 = kyberPacked)
    (hx23 : s.readReg64 .x23 = opkIdIsSome.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = opkPacked) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1778#64) s
      (((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
       ((coroPtr + 0xf8#64) ↦₆₄ ss0) ∗
       ((coroPtr + 0x250#64) ↦₆₄ u_250) ∗
       ((coroPtr + 0x258#64) ↦₆₄ u_258) ∗
       ((coroPtr + 0x260#64) ↦₆₄ u_260) ∗
       ((coroPtr + 0x268#64) ↦₃₂ u_268) ∗
       ((coroPtr + 0x26c#64) ↦₃₂ u_26c) ∗
       ((coroPtr + 0x270#64) ↦₆₄ u_270) ∗
       ((coroPtr + 0x278#64) ↦₆₄ u_278) ∗
       ((coroPtr + 0x298#64) ↦₆₄ u_298) ∗
       ((coroPtr + 0x2a0#64) ↦₆₄ u_2a0) ∗
       ((coroPtr + 0x2a8#64) ↦₃₂ u_2a8) ∗
       ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
       ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
       ((s.sp + 0x80#64) ↦₆₄ u_80) ∗
       ((s.sp + 0x88#64) ↦₆₄ u_88) ∗
       ((s.sp + 0x90#64) ↦₆₄ u_90) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₃₂ u_b8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ signedPreKeyId.zeroExtend 64) ∗
       ((s.sp + 0x3a0#64) ↦₆₄ u_3a0) ∗
       ((s.sp + 0x3ac#64) ↦₈ b_3ac) ∗
       ((s.sp + 0x3b0#64) ↦₆₄ (u_3b0)) ∗
       ((s.sp + 0x3b8#64) ↦₆₄ u_3b8) ∗
       ((s.sp + 0x3c0#64) ↦₆₄ u_3c0) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ u_3c8) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ u_3d0) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ u_3d8))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
          ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
          ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
          ((coroPtr + 0xf8#64) ↦₆₄ ss0) ∗
          ((coroPtr + 0x250#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((coroPtr + 0x258#64) ↦₆₄ opkPacked) ∗
          ((coroPtr + 0x260#64) ↦₆₄ kyberPacked) ∗
          ((coroPtr + 0x268#64) ↦₃₂ signedPreKeyId) ∗
          ((coroPtr + 0x26c#64) ↦₃₂ (s.readReg64 (Reg.gpr 11#5)).truncate 32) ∗
          ((coroPtr + 0x270#64) ↦₆₄ v_330) ∗
          ((coroPtr + 0x278#64) ↦₆₄ v_388) ∗
          ((coroPtr + 0x298#64) ↦₆₄ opkPacked) ∗
          ((coroPtr + 0x2a0#64) ↦₆₄ kyberPacked) ∗
          ((coroPtr + 0x2a8#64) ↦₃₂ signedPreKeyId) ∗
          ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
          ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
          ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
          ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          ((s.sp + 0x90#64) ↦₆₄ v_388) ∗
          ((s.sp + 0xa0#64) ↦₆₄ localAddrPtr) ∗
          ((s.sp + 0xa8#64) ↦₆₄ v_330) ∗
          ((s.sp + 0xb0#64) ↦₆₄ msgPtr) ∗
          ((s.sp + 0xb8#64) ↦₃₂ msgVerByte.zeroExtend 32) ∗
          ((s.sp + 0xd0#64) ↦₆₄ signedPreKeyId.zeroExtend 64) ∗
          ((s.sp + 0x3a0#64) ↦₆₄ remoteAddrPtr) ∗
          ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
          ((s.sp + 0x3b0#64) ↦₆₄ (s.sp + 0x3ac#64)) ∗
          ((s.sp + 0x3b8#64) ↦₆₄ msgPtr) ∗
          ((s.sp + 0x3c0#64) ↦₆₄ (s.sp + 0x3a0#64)) ∗
          ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ 8#64) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 0#64)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x8 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x9 = 8#64 ∧
        s1.readReg64 .x10 = msgVerByte.zeroExtend 64 ∧
        s1.readReg64 .x11 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x22 = kyberPacked ∧
        s1.readReg64 .x23 = opkPacked ∧
        s1.readReg64 .x24 = opkPacked ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_330 ∧
        s1.readReg64 .x27 = s.sp + 0x370#64 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  have hss0_beq : (ss0 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hss0_ne
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1698 0x16b0
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x16c8 0x1774
  dsimp only [trTrapProgAt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = 0xfffffffffffffffe#64 := hx20
  have hx22' : s.readReg64 (Reg.gpr 22#5) = kyberPacked := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = opkIdIsSome.zeroExtend 64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = opkPacked := hx24
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  have hbfm1 : ((opkIdIsSome.zeroExtend 64 &&& 255#64) |||
    ((opkPacked >>> 8 &&& 72057594037927935#64) <<< 8)) = opkPacked := by
    revert hpack_lo; clear * -; bv_slice
  refine ⟨?_, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
  rw [hbfm1]
  exact Entails.of_eq (by ac_rfl)

/-- Segment P2.6f (`+0x1698 → +0x1778`): stores `Ok((opkId?, kyberPreKeyId?, signedPreKeyId))` and
initializes the Stage P3 decryption loop frame on the stack. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg6f_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr msgPtr remoteAddrPtr localAddrPtr
    opkPacked kyberPacked ss0 v_330 v_388
    u_250 u_258 u_260 u_270 u_278 u_298 u_2a0
    u_80 u_88 u_90 u_a0 u_a8 u_b0
    u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
    (opkIdIsSome signedPreKeyId u_268 u_26c u_2a8 u_b8 : BitVec 32)
    (msgVerByte b_390 b_3ac : BitVec 8)
    (hss0_ne : ss0 + 1#64 ≠ 0#64)
    (hpack_lo : (opkPacked &&& 0xff#64) = (opkIdIsSome.zeroExtend 64 &&& 0xff#64))
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1698#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = 0xfffffffffffffffe#64)
    (hx22 : s.readReg64 .x22 = kyberPacked)
    (hx23 : s.readReg64 .x23 = opkIdIsSome.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = opkPacked) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1778#64) s
      (((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
       ((coroPtr + 0xf8#64) ↦₆₄ ss0) ∗
       ((coroPtr + 0x250#64) ↦₆₄ u_250) ∗
       ((coroPtr + 0x258#64) ↦₆₄ u_258) ∗
       ((coroPtr + 0x260#64) ↦₆₄ u_260) ∗
       ((coroPtr + 0x268#64) ↦₃₂ u_268) ∗
       ((coroPtr + 0x26c#64) ↦₃₂ u_26c) ∗
       ((coroPtr + 0x270#64) ↦₆₄ u_270) ∗
       ((coroPtr + 0x278#64) ↦₆₄ u_278) ∗
       ((coroPtr + 0x298#64) ↦₆₄ u_298) ∗
       ((coroPtr + 0x2a0#64) ↦₆₄ u_2a0) ∗
       ((coroPtr + 0x2a8#64) ↦₃₂ u_2a8) ∗
       ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
       ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
       ((s.sp + 0x80#64) ↦₆₄ u_80) ∗
       ((s.sp + 0x88#64) ↦₆₄ u_88) ∗
       ((s.sp + 0x90#64) ↦₆₄ u_90) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₃₂ u_b8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ signedPreKeyId.zeroExtend 64) ∗
       ((s.sp + 0x3a0#64) ↦₆₄ u_3a0) ∗
       ((s.sp + 0x3ac#64) ↦₈ b_3ac) ∗
       ((s.sp + 0x3b0#64) ↦₆₄ u_3b0) ∗
       ((s.sp + 0x3b8#64) ↦₆₄ u_3b8) ∗
       ((s.sp + 0x3c0#64) ↦₆₄ u_3c0) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ u_3c8) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ u_3d0) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ u_3d8))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
          ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
          ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
          ((coroPtr + 0xf8#64) ↦₆₄ ss0) ∗
          ((coroPtr + 0x250#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((coroPtr + 0x258#64) ↦₆₄ opkPacked) ∗
          ((coroPtr + 0x260#64) ↦₆₄ kyberPacked) ∗
          ((coroPtr + 0x268#64) ↦₃₂ signedPreKeyId) ∗
          ((coroPtr + 0x26c#64) ↦₃₂ (s.readReg64 (Reg.gpr 11#5)).truncate 32) ∗
          ((coroPtr + 0x270#64) ↦₆₄ v_330) ∗
          ((coroPtr + 0x278#64) ↦₆₄ v_388) ∗
          ((coroPtr + 0x298#64) ↦₆₄ opkPacked) ∗
          ((coroPtr + 0x2a0#64) ↦₆₄ kyberPacked) ∗
          ((coroPtr + 0x2a8#64) ↦₃₂ signedPreKeyId) ∗
          ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
          ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
          ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
          ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          ((s.sp + 0x90#64) ↦₆₄ v_388) ∗
          ((s.sp + 0xa0#64) ↦₆₄ localAddrPtr) ∗
          ((s.sp + 0xa8#64) ↦₆₄ v_330) ∗
          ((s.sp + 0xb0#64) ↦₆₄ msgPtr) ∗
          ((s.sp + 0xb8#64) ↦₃₂ msgVerByte.zeroExtend 32) ∗
          ((s.sp + 0xd0#64) ↦₆₄ signedPreKeyId.zeroExtend 64) ∗
          ((s.sp + 0x3a0#64) ↦₆₄ remoteAddrPtr) ∗
          ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
          ((s.sp + 0x3b0#64) ↦₆₄ (s.sp + 0x3ac#64)) ∗
          ((s.sp + 0x3b8#64) ↦₆₄ msgPtr) ∗
          ((s.sp + 0x3c0#64) ↦₆₄ (s.sp + 0x3a0#64)) ∗
          ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ 8#64) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 0#64)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x8 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x9 = 8#64 ∧
        s1.readReg64 .x10 = msgVerByte.zeroExtend 64 ∧
        s1.readReg64 .x11 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x22 = kyberPacked ∧
        s1.readReg64 .x23 = opkPacked ∧
        s1.readReg64 .x24 = opkPacked ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_330 ∧
        s1.readReg64 .x27 = s.sp + 0x370#64 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg6f_wp_trap b C abs s
      coroPtr msgPtr remoteAddrPtr localAddrPtr opkPacked kyberPacked ss0 v_330 v_388
      u_250 u_258 u_260 u_270 u_278 u_298 u_2a0 u_80 u_88 u_90 u_a0 u_a8 u_b0
      u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 opkIdIsSome signedPreKeyId u_268 u_26c u_2a8 u_b8
      msgVerByte b_390 b_3ac hss0_ne hpack_lo hpc hrun hsp_align hx19 hx20 hx22 hx23 hx24)

end CryptoVerification.E2E.Pqxdh.ResponderClosure
