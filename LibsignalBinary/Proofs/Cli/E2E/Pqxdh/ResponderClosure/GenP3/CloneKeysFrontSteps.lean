/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneFetch
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4K
public import ProofLib.SepLogic.WP
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysBase
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpoch
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

@[expose] public section

set_option autoImplicit false

/-!
# General Stage P3 Clone — Segment 1 Step Helpers

Basic-block `SepWP` step lemmas (`seg1a_wp`..`seg4_none_wp`, `+0x1778 → +0x19b0`) for Segment 1.
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
  (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#4]")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")

/-! ## 1. Non-Nil Step Helpers for Front (`+0x1778 .. +0x19b0`) -/

/- `local_identity_public` pre-alloc step (`+0x1778 → +0x179c`, `locIdLen ≠ 0`). -/
set_option maxHeartbeats 400000 in
theorem seg1a_4k_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContractsMem4K b A ext)
    (s : State) (coroPtr locIdPtr locIdLen u_d0 : BitVec 64)
    (sessionVer u_7c : BitVec 32)
    (hlen_nz : locIdLen ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1778#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x179c#64) s
      (((coroPtr + 0x100#64) ↦₆₄ locIdPtr) ∗
       ((coroPtr + 0x108#64) ↦₆₄ locIdLen) ∗
       ((coroPtr + 0x240#64) ↦₃₂ sessionVer) ∗
       ((s.sp + 0x7c#64) ↦₃₂ u_7c) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x100#64) ↦₆₄ locIdPtr) ∗
          ((coroPtr + 0x108#64) ↦₆₄ locIdLen) ∗
          ((coroPtr + 0x240#64) ↦₃₂ sessionVer) ∗
          ((s.sp + 0x7c#64) ↦₃₂ sessionVer) ∗
          ((s.sp + 0xd0#64) ↦₆₄ locIdLen)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = locIdLen ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = locIdPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hshim := closure_shim_4k_ok b ext hA
  have hlen_beq : (locIdLen == 0#64) = false := beq_eq_false_iff_ne.mpr hlen_nz
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1778 0x1798
  dsimp only [tripleRatchetProgAtExt] at hshim hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  wp_call hshim ()
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

theorem seg1a_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContracts b A ext) :
    ∀ (s : State) (coroPtr locIdPtr locIdLen u_d0 : BitVec 64)
      (sessionVer u_7c : BitVec 32),
      locIdLen ≠ 0#64 →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1778#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      s.readReg64 .x19 = coroPtr →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x179c#64) s
        (((coroPtr + 0x100#64) ↦₆₄ locIdPtr) ∗
         ((coroPtr + 0x108#64) ↦₆₄ locIdLen) ∗
         ((coroPtr + 0x240#64) ↦₃₂ sessionVer) ∗
         ((s.sp + 0x7c#64) ↦₃₂ u_7c) ∗
         ((s.sp + 0xd0#64) ↦₆₄ u_d0))
        (fun s1 P_f =>
          (P_f ⊢
            ((coroPtr + 0x100#64) ↦₆₄ locIdPtr) ∗
            ((coroPtr + 0x108#64) ↦₆₄ locIdLen) ∗
            ((coroPtr + 0x240#64) ↦₃₂ sessionVer) ∗
            ((s.sp + 0x7c#64) ↦₃₂ sessionVer) ∗
            ((s.sp + 0xd0#64) ↦₆₄ locIdLen)) ∧
          s1.sp = s.sp ∧
          s1.trace = s.trace ∧
          s1.readReg64 .x0 = locIdLen ∧
          s1.readReg64 .x1 = 1#64 ∧
          s1.readReg64 .x19 = coroPtr ∧
          s1.readReg64 .x21 = locIdPtr ∧
          s1.readReg64 .x27 = s.readReg64 .x27 ∧
          s1.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s) :=
  seg1a_4k_wp b ext (AllocContractsMem4K.of_AllocContracts hA)

/- `local_identity_public` post-alloc `memcpy` step (`+0x17a0 → +0x18e0`, 4K stack). -/
set_option maxHeartbeats 400000 in
theorem seg1b_4k_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContractsMem4K b A ext)
    (s : State) (coroPtr locIdPtr newLocIdPtr : BitVec 64)
    (locIdBytes : List (BitVec 8))
    (hnew_nz : newLocIdPtr ≠ 0#64)
    (hlen_lt : locIdBytes.length < 2 ^ 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x17a0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = newLocIdPtr)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = locIdPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x18e0#64) s
      (((s.sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 locIdBytes.length) ∗
       (locIdPtr ↦ₛ locIdBytes) ∗
       memRegion newLocIdPtr locIdBytes.length ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 locIdBytes.length) ∗
          (locIdPtr ↦ₛ locIdBytes) ∗
          (newLocIdPtr ↦ₛ locIdBytes) ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x23 = newLocIdPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hmemcpy := closure_memcpy_4k_ok b ext hA
  have hnew_beq : (newLocIdPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hnew_nz
  closure_fetches_range_cli b (Rust.withPanics ext) 0x17a0 0x17b4
  dsimp only [tripleRatchetProgAtExt, withStack] at hmemcpy hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = newLocIdPtr := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = locIdPtr := hx21
  wp_steps
  wp_call hmemcpy (newLocIdPtr, locIdPtr, locIdBytes)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/- `local_identity_public` post-alloc `memcpy` step (`+0x17a0 → +0x18e0`). -/
set_option maxHeartbeats 400000 in
theorem seg1b_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContracts b A ext)
    (s : State) (coroPtr locIdPtr newLocIdPtr : BitVec 64)
    (locIdBytes : List (BitVec 8))
    (hnew_nz : newLocIdPtr ≠ 0#64)
    (hlen_lt : locIdBytes.length < 2 ^ 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x17a0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = newLocIdPtr)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = locIdPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x18e0#64) s
      (((s.sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 locIdBytes.length) ∗
       (locIdPtr ↦ₛ locIdBytes) ∗
       memRegion newLocIdPtr locIdBytes.length)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 locIdBytes.length) ∗
          (locIdPtr ↦ₛ locIdBytes) ∗
          (newLocIdPtr ↦ₛ locIdBytes)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x23 = newLocIdPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hmemcpy := closure_memcpy_ok b ext hA
  have hnew_beq : (newLocIdPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hnew_nz
  closure_fetches_range_cli b (Rust.withPanics ext) 0x17a0 0x17b4
  dsimp only [tripleRatchetProgAtExt] at hmemcpy hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = newLocIdPtr := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = locIdPtr := hx21
  wp_steps
  wp_call hmemcpy (newLocIdPtr, locIdPtr, locIdBytes)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/- `remote_identity_public` pre-alloc step (`+0x18e0 → +0x18fc`, `remIdLen ≠ 0`). -/
set_option maxHeartbeats 400000 in
theorem seg2a_4k_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContractsMem4K b A ext)
    (s : State) (coroPtr remIdPtr remIdLen : BitVec 64)
    (hlen_nz : remIdLen ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x18e0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x18fc#64) s
      (((coroPtr + 0x118#64) ↦₆₄ remIdPtr) ∗
       ((coroPtr + 0x120#64) ↦₆₄ remIdLen))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x118#64) ↦₆₄ remIdPtr) ∗
          ((coroPtr + 0x120#64) ↦₆₄ remIdLen)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = remIdLen ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = remIdPtr ∧
        s1.readReg64 .x22 = s.sp + 0x930#64 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = remIdLen ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hshim := closure_shim_4k_ok b ext hA
  have hlen_beq : (remIdLen == 0#64) = false := beq_eq_false_iff_ne.mpr hlen_nz
  closure_fetches_range_cli b (Rust.withPanics ext) 0x18e0 0x18f8
  dsimp only [tripleRatchetProgAtExt] at hshim hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  wp_call hshim ()
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

theorem seg2a_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContracts b A ext) :
    ∀ (s : State) (coroPtr remIdPtr remIdLen : BitVec 64),
      remIdLen ≠ 0#64 →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x18e0#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      s.readReg64 .x19 = coroPtr →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x18fc#64) s
        (((coroPtr + 0x118#64) ↦₆₄ remIdPtr) ∗
         ((coroPtr + 0x120#64) ↦₆₄ remIdLen))
        (fun s1 P_f =>
          (P_f ⊢
            ((coroPtr + 0x118#64) ↦₆₄ remIdPtr) ∗
            ((coroPtr + 0x120#64) ↦₆₄ remIdLen)) ∧
          s1.sp = s.sp ∧
          s1.trace = s.trace ∧
          s1.readReg64 .x0 = remIdLen ∧
          s1.readReg64 .x1 = 1#64 ∧
          s1.readReg64 .x19 = coroPtr ∧
          s1.readReg64 .x21 = remIdPtr ∧
          s1.readReg64 .x22 = s.sp + 0x930#64 ∧
          s1.readReg64 .x23 = s.readReg64 .x23 ∧
          s1.readReg64 .x24 = remIdLen ∧
          s1.readReg64 .x27 = s.readReg64 .x27 ∧
          s1.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s) :=
  seg2a_4k_wp b ext (AllocContractsMem4K.of_AllocContracts hA)

/- `remote_identity_public` post-alloc `memcpy` step (`+0x1900 → +0x191c`, 4K stack). -/
set_option maxHeartbeats 400000 in
theorem seg2b_4k_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContractsMem4K b A ext)
    (s : State) (coroPtr remIdPtr newRemIdPtr : BitVec 64)
    (remIdBytes : List (BitVec 8))
    (hnew_nz : newRemIdPtr ≠ 0#64)
    (hlen_lt : remIdBytes.length < 2 ^ 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1900#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = newRemIdPtr)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = remIdPtr)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 remIdBytes.length) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x191c#64) s
      ((remIdPtr ↦ₛ remIdBytes) ∗
       memRegion newRemIdPtr remIdBytes.length ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          (remIdPtr ↦ₛ remIdBytes) ∗
          (newRemIdPtr ↦ₛ remIdBytes) ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = BitVec.ofNat 64 remIdBytes.length ∧
        s1.readReg64 .x25 = newRemIdPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hmemcpy := closure_memcpy_4k_ok b ext hA
  have hnew_beq : (newRemIdPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hnew_nz
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1900 0x1914
  dsimp only [tripleRatchetProgAtExt, withStack] at hmemcpy hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = newRemIdPtr := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = remIdPtr := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 remIdBytes.length := hx24
  wp_steps
  wp_call hmemcpy (newRemIdPtr, remIdPtr, remIdBytes)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/- `remote_identity_public` post-alloc `memcpy` step (`+0x1900 → +0x191c`). -/
set_option maxHeartbeats 400000 in
theorem seg2b_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContracts b A ext)
    (s : State) (coroPtr remIdPtr newRemIdPtr : BitVec 64)
    (remIdBytes : List (BitVec 8))
    (hnew_nz : newRemIdPtr ≠ 0#64)
    (hlen_lt : remIdBytes.length < 2 ^ 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1900#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = newRemIdPtr)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = remIdPtr)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 remIdBytes.length) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x191c#64) s
      ((remIdPtr ↦ₛ remIdBytes) ∗
       memRegion newRemIdPtr remIdBytes.length)
      (fun s1 P_f =>
        (P_f ⊢
          (remIdPtr ↦ₛ remIdBytes) ∗
          (newRemIdPtr ↦ₛ remIdBytes)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = BitVec.ofNat 64 remIdBytes.length ∧
        s1.readReg64 .x25 = newRemIdPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hmemcpy := closure_memcpy_ok b ext hA
  have hnew_beq : (newRemIdPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hnew_nz
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1900 0x1914
  dsimp only [tripleRatchetProgAtExt] at hmemcpy hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = newRemIdPtr := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = remIdPtr := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 remIdBytes.length := hx24
  wp_steps
  wp_call hmemcpy (newRemIdPtr, remIdPtr, remIdBytes)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/- `root_key` pre-alloc step (`+0x191c → +0x1938`, `rootKeyLen ≠ 0`). -/
set_option maxHeartbeats 400000 in
theorem seg3a_4k_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContractsMem4K b A ext)
    (s : State) (coroPtr rootKeyPtr rootKeyLen u_98 : BitVec 64)
    (hlen_nz : rootKeyLen ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x191c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1938#64) s
      (((coroPtr + 0x130#64) ↦₆₄ rootKeyPtr) ∗
       ((coroPtr + 0x138#64) ↦₆₄ rootKeyLen) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x130#64) ↦₆₄ rootKeyPtr) ∗
          ((coroPtr + 0x138#64) ↦₆₄ rootKeyLen) ∗
          ((s.sp + 0x98#64) ↦₆₄ rootKeyLen)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = rootKeyLen ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = rootKeyPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = rootKeyLen ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hshim := closure_shim_4k_ok b ext hA
  have hlen_beq : (rootKeyLen == 0#64) = false := beq_eq_false_iff_ne.mpr hlen_nz
  closure_fetches_range_cli b (Rust.withPanics ext) 0x191c 0x1934
  dsimp only [tripleRatchetProgAtExt] at hshim hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  wp_call hshim ()
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem seg3a_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContracts b A ext) :
    ∀ (s : State) (coroPtr rootKeyPtr rootKeyLen u_98 : BitVec 64),
      rootKeyLen ≠ 0#64 →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x191c#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      s.readReg64 .x19 = coroPtr →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1938#64) s
        (((coroPtr + 0x130#64) ↦₆₄ rootKeyPtr) ∗
         ((coroPtr + 0x138#64) ↦₆₄ rootKeyLen) ∗
         ((s.sp + 0x98#64) ↦₆₄ u_98))
        (fun s1 P_f =>
          (P_f ⊢
            ((coroPtr + 0x130#64) ↦₆₄ rootKeyPtr) ∗
            ((coroPtr + 0x138#64) ↦₆₄ rootKeyLen) ∗
            ((s.sp + 0x98#64) ↦₆₄ rootKeyLen)) ∧
          s1.sp = s.sp ∧
          s1.trace = s.trace ∧
          s1.readReg64 .x0 = rootKeyLen ∧
          s1.readReg64 .x1 = 1#64 ∧
          s1.readReg64 .x19 = coroPtr ∧
          s1.readReg64 .x21 = rootKeyPtr ∧
          s1.readReg64 .x22 = s.readReg64 .x22 ∧
          s1.readReg64 .x23 = s.readReg64 .x23 ∧
          s1.readReg64 .x24 = s.readReg64 .x24 ∧
          s1.readReg64 .x25 = s.readReg64 .x25 ∧
          s1.readReg64 .x26 = rootKeyLen ∧
          s1.readReg64 .x27 = s.readReg64 .x27 ∧
          s1.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s) :=
  seg3a_4k_wp b ext (AllocContractsMem4K.of_AllocContracts hA)

/- `root_key` post-alloc `memcpy` step (`+0x193c → +0x195c`, 4K stack). -/
set_option maxHeartbeats 400000 in
theorem seg3b_4k_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContractsMem4K b A ext)
    (s : State) (coroPtr rootKeyPtr newRootKeyPtr u_50 : BitVec 64)
    (rootKeyBytes : List (BitVec 8))
    (hnew_nz : newRootKeyPtr ≠ 0#64)
    (hlen_lt : rootKeyBytes.length < 2 ^ 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x193c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = newRootKeyPtr)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = rootKeyPtr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 rootKeyBytes.length) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x195c#64) s
      (((s.sp + 0x50#64) ↦₆₄ u_50) ∗
       (rootKeyPtr ↦ₛ rootKeyBytes) ∗
       memRegion newRootKeyPtr rootKeyBytes.length ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗
          (rootKeyPtr ↦ₛ rootKeyBytes) ∗
          (newRootKeyPtr ↦ₛ rootKeyBytes) ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hmemcpy := closure_memcpy_4k_ok b ext hA
  have hnew_beq : (newRootKeyPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hnew_nz
  closure_fetches_range_cli b (Rust.withPanics ext) 0x193c 0x1950
  dsimp only [tripleRatchetProgAtExt, withStack] at hmemcpy hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = newRootKeyPtr := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = rootKeyPtr := hx21
  have hx26' : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 rootKeyBytes.length := hx26
  wp_steps
  wp_call hmemcpy (newRootKeyPtr, rootKeyPtr, rootKeyBytes)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/- `root_key` post-alloc `memcpy` step (`+0x193c → +0x195c`). -/
set_option maxHeartbeats 400000 in
theorem seg3b_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContracts b A ext)
    (s : State) (coroPtr rootKeyPtr newRootKeyPtr u_50 : BitVec 64)
    (rootKeyBytes : List (BitVec 8))
    (hnew_nz : newRootKeyPtr ≠ 0#64)
    (hlen_lt : rootKeyBytes.length < 2 ^ 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x193c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = newRootKeyPtr)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = rootKeyPtr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 rootKeyBytes.length) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x195c#64) s
      (((s.sp + 0x50#64) ↦₆₄ u_50) ∗
       (rootKeyPtr ↦ₛ rootKeyBytes) ∗
       memRegion newRootKeyPtr rootKeyBytes.length)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗
          (rootKeyPtr ↦ₛ rootKeyBytes) ∗
          (newRootKeyPtr ↦ₛ rootKeyBytes)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hmemcpy := closure_memcpy_ok b ext hA
  have hnew_beq : (newRootKeyPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hnew_nz
  closure_fetches_range_cli b (Rust.withPanics ext) 0x193c 0x1950
  dsimp only [tripleRatchetProgAtExt] at hmemcpy hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = newRootKeyPtr := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = rootKeyPtr := hx21
  have hx26' : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 rootKeyBytes.length := hx26
  wp_steps
  wp_call hmemcpy (newRootKeyPtr, rootKeyPtr, rootKeyBytes)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/- `sender_chain = Some` pre-call step (`+0x195c → Chain::clone`). -/
set_option maxHeartbeats 400000 in
theorem seg4a1_wp (b : BitVec 64)
    (ext : String → Option (State → State))
    (s : State) (coroPtr sc0 : BitVec 64)
    (prevCounter u_5c : BitVec 32)
    (hsc_ne : sc0 + 1#64 ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x195c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3.chainClone3Name) s
      (((coroPtr + 0x188#64) ↦₆₄ sc0) ∗
       ((coroPtr + 0x244#64) ↦₃₂ prevCounter) ∗
       ((s.sp + 0x5c#64) ↦₃₂ u_5c))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x188#64) ↦₆₄ sc0) ∗
          ((coroPtr + 0x244#64) ↦₃₂ prevCounter) ∗
          ((s.sp + 0x5c#64) ↦₃₂ prevCounter)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x1 = coroPtr + 0x188#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
            0x197c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsc_beq : (sc0 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hsc_ne
  closure_fetches_range_cli b (Rust.withPanics ext) 0x195c 0x1978
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have hcc : (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3.chainClone3Name =
      b + (bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#4]")) := by
    dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3.chainClone3Name]
    rw [Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#4]")]
  have htarget : (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
      0x1978#64 + bv% ((2^64 + ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#4]" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 6520)) % 2^64) =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3.chainClone3Name := by
    rw [hentry, hcc]; bv_omega
  clear hentry hcc
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by rw [← htarget]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/- `sender_chain = Some` post-call copy (`+0x197c → +0x19b0`). -/
set_option maxHeartbeats 400000 in
theorem seg4a2_wp (b : BitVec 64)
    (ext : String → Option (State → State))
    (s : State) (coroPtr u_48
    c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
    u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x197c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = s.sp + 0x930#64)
    (hx27 : s.readReg64 .x27 = s.sp + 0x370#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x19b0#64) s
      (((s.sp + 0x48#64) ↦₆₄ u_48) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ c0) ∗ ((s.sp + 0x3e8#64) ↦₆₄ c1) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ c2) ∗ ((s.sp + 0x3f8#64) ↦₆₄ c3) ∗
       ((s.sp + 0x400#64) ↦₆₄ c4) ∗ ((s.sp + 0x408#64) ↦₆₄ c5) ∗
       ((s.sp + 0x410#64) ↦₆₄ c6) ∗ ((s.sp + 0x418#64) ↦₆₄ c7) ∗
       ((s.sp + 0x420#64) ↦₆₄ c8) ∗ ((s.sp + 0x428#64) ↦₆₄ c9) ∗
       ((s.sp + 0x430#64) ↦₆₄ c10) ∗ ((s.sp + 0x438#64) ↦₆₄ c11) ∗
       ((s.sp + 0x440#64) ↦₆₄ c12) ∗
       ((s.sp + 0x930#64) ↦₆₄ u930) ∗ ((s.sp + 0x938#64) ↦₆₄ u938) ∗
       ((s.sp + 0x940#64) ↦₆₄ u940) ∗ ((s.sp + 0x948#64) ↦₆₄ u948) ∗
       ((s.sp + 0x950#64) ↦₆₄ u950) ∗ ((s.sp + 0x958#64) ↦₆₄ u958) ∗
       ((s.sp + 0x960#64) ↦₆₄ u960) ∗ ((s.sp + 0x968#64) ↦₆₄ u968) ∗
       ((s.sp + 0x970#64) ↦₆₄ u970) ∗ ((s.sp + 0x978#64) ↦₆₄ u978) ∗
       ((s.sp + 0x980#64) ↦₆₄ u980) ∗ ((s.sp + 0x988#64) ↦₆₄ u988))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x48#64) ↦₆₄ c0) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ c0) ∗ ((s.sp + 0x3e8#64) ↦₆₄ c1) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ c2) ∗ ((s.sp + 0x3f8#64) ↦₆₄ c3) ∗
          ((s.sp + 0x400#64) ↦₆₄ c4) ∗ ((s.sp + 0x408#64) ↦₆₄ c5) ∗
          ((s.sp + 0x410#64) ↦₆₄ c6) ∗ ((s.sp + 0x418#64) ↦₆₄ c7) ∗
          ((s.sp + 0x420#64) ↦₆₄ c8) ∗ ((s.sp + 0x428#64) ↦₆₄ c9) ∗
          ((s.sp + 0x430#64) ↦₆₄ c10) ∗ ((s.sp + 0x438#64) ↦₆₄ c11) ∗
          ((s.sp + 0x440#64) ↦₆₄ c12) ∗
          ((s.sp + 0x930#64) ↦₆₄ c1) ∗ ((s.sp + 0x938#64) ↦₆₄ c2) ∗
          ((s.sp + 0x940#64) ↦₆₄ c3) ∗ ((s.sp + 0x948#64) ↦₆₄ c4) ∗
          ((s.sp + 0x950#64) ↦₆₄ c5) ∗ ((s.sp + 0x958#64) ↦₆₄ c6) ∗
          ((s.sp + 0x960#64) ↦₆₄ c7) ∗ ((s.sp + 0x968#64) ↦₆₄ c8) ∗
          ((s.sp + 0x970#64) ↦₆₄ c9) ∗ ((s.sp + 0x978#64) ↦₆₄ c10) ∗
          ((s.sp + 0x980#64) ↦₆₄ c11) ∗ ((s.sp + 0x988#64) ↦₆₄ c12)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = s.sp + 0x370#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 0x197c 0x19a8
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = s.sp + 0x930#64 := hx22
  have hx27' : s.readReg64 (Reg.gpr 27#5) = s.sp + 0x370#64 := hx27
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-! ## 2. Nil-Path Step Helpers for Front (`+0x18e0`, `+0x195c`) -/

/- `remote_identity_public` empty fast-path (`+0x18e0 → +0x191c`, `remIdLen = 0`). -/
set_option maxHeartbeats 400000 in
theorem seg2_nil_wp (b : BitVec 64)
    (ext : String → Option (State → State))
    (s : State) (coroPtr : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x18e0#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x191c#64) s
      ((coroPtr + 0x120#64) ↦₆₄ 0#64)
      (fun s1 P_f =>
        (P_f ⊢ ((coroPtr + 0x120#64) ↦₆₄ 0#64)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.sp + 0x930#64 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = 0#64 ∧
        s1.readReg64 .x25 = 1#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 0x18e0 0x1918
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/- `sender_chain = None` inline fast-path (`+0x195c → +0x19b0`, `sc0 = noneCap`). -/
set_option maxHeartbeats 400000 in
theorem seg4_none_wp (b : BitVec 64)
    (ext : String → Option (State → State))
    (s : State) (coroPtr u_48 : BitVec 64)
    (prevCounter u_5c : BitVec 32)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x195c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x19b0#64) s
      (((coroPtr + 0x188#64) ↦₆₄ noneCap) ∗
       ((coroPtr + 0x244#64) ↦₃₂ prevCounter) ∗
       ((s.sp + 0x48#64) ↦₆₄ u_48) ∗
       ((s.sp + 0x5c#64) ↦₃₂ u_5c))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x188#64) ↦₆₄ noneCap) ∗
          ((coroPtr + 0x244#64) ↦₃₂ prevCounter) ∗
          ((s.sp + 0x48#64) ↦₆₄ noneCap) ∗
          ((s.sp + 0x5c#64) ↦₃₂ prevCounter)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 0x195c 0x19ac
  dsimp only [tripleRatchetProgAtExt, noneCap] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1
