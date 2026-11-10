/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Stage P4.3 Segments: `PreKeyStore::remove_pre_key`

Basic-block `SepWP` segments (`+0x3c0 → removePoll`, `+0xc8 → removeFutDrop`, `+0x298 → +0x3cc` /
`+0x550`) and vtable helpers for Substage P4.3 (`opkIdIsSome = 1#32`) on
`tripleRatchetProgAtExt img.base ext`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")

/-! ## Basic-block `SepWP` segments for Substage P4.3 -/

/-- `+0x3c0 → removePreKeyPollAddr` (via `+0xb8..+0xc4`): stores
    `(removePreKeyFutPtr, removePreKeyFutVt)` at `coroPtr + 0x2c8..0x2d0` and polls into
    `sp + 0x3e0..0x410`. -/
theorem p4_seg3a_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr ctxPtr removePreKeyFutPtr removePreKeyFutVt removePreKeyPollAddr
    u_2c8 u_2d0 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3c0#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = removePreKeyFutPtr)
    (hx1 : s.readReg64 .x1 = removePreKeyFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr) :
    SepWP (tripleRatchetProgAtExt b ext) removePreKeyPollAddr s
      (((coroPtr + 0x2c8#64) ↦₆₄ u_2c8) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ u_2d0) ∗
       ((removePreKeyFutVt + 0x18#64) ↦₆₄ᵣ removePreKeyPollAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x2c8#64) ↦₆₄ removePreKeyFutPtr) ∗
          ((coroPtr + 0x2d0#64) ↦₆₄ removePreKeyFutVt) ∗
          ((removePreKeyFutVt + 0x18#64) ↦₆₄ᵣ removePreKeyPollAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = removePreKeyFutPtr ∧
        s1.readReg64 .x1 = ctxPtr ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xc8#64) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 0x3c0 0x3c8
  closure_fetches_range_cli b (Rust.withPanics ext) 0xb8 0xc4
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = removePreKeyFutPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = removePreKeyFutVt := hx1
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx27' : s.readReg64 (Reg.gpr 27#5) = ctxPtr := hx27
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- `+0xc8 → removePreKeyDropAddr` (via `+0x268..+0x294`) for any ready tag `w0`
    (`w0 + 3#64 ≠ 0#64`, covering both `Ok(())` and `Err(e)`):
    copies `sp + 0x3ec..0x410` into `sp + 0x310..0x334`, sets `x22 := o1.zeroExtend 64`,
    `x28 := w0`, and calls `drop_in_place` (`[removePreKeyFutVt]`) on `removePreKeyFutPtr`. -/
theorem p4_seg3b_gen_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr removePreKeyFutPtr removePreKeyFutVt removePreKeyDropAddr w0
    o2 o3 o4 o5 u_310 u_318 u_320 u_328 : BitVec 64)
    (o1 o6 u_330 : BitVec 32)
    (hw0_ne_pend : w0 + 3#64 ≠ 0#64)
    (hdrop_nz : removePreKeyDropAddr ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xc8#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) :
    SepWP (tripleRatchetProgAtExt b ext) removePreKeyDropAddr s
      (((coroPtr + 0x2c8#64) ↦₆₄ removePreKeyFutPtr) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ removePreKeyFutVt) ∗
       (removePreKeyFutVt ↦₆₄ᵣ removePreKeyDropAddr) ∗
       stagingCellsAt (s.sp + 0x310#64) u_310 u_318 u_320 u_328 u_330 ∗
       pollCellsAt (s.sp + 0x3e0#64) w0 o1 o2 o3 o4 o5 o6)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x2c8#64) ↦₆₄ removePreKeyFutPtr) ∗
          ((coroPtr + 0x2d0#64) ↦₆₄ removePreKeyFutVt) ∗
          (removePreKeyFutVt ↦₆₄ᵣ removePreKeyDropAddr) ∗
          stagingCellsAt (s.sp + 0x310#64) o2 o3 o4 o5 o6 ∗
          pollCellsAt (s.sp + 0x3e0#64) w0 o1 o2 o3 o4 o5 o6) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = removePreKeyFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = removePreKeyFutPtr ∧
        s1.readReg64 .x22 = o1.zeroExtend 64 ∧
        s1.readReg64 .x23 = removePreKeyFutVt ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = w0 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x298#64) := by
  have hw0_beq : (w0 + 3#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hw0_ne_pend
  have hdrop_beq : (removePreKeyDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  unfold stagingCellsAt pollCellsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  closure_fetches_range_cli b (Rust.withPanics ext) 0xc8 0xd0
  closure_fetches_range_cli b (Rust.withPanics ext) 0x268 0x294
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by simp only [BitVec.add_zero]), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- `+0x298 → +0x3cc` (`Ok(())`, `x28 = -2`): deallocates `removePreKeyFutPtr` and branches at
    `+0x2b0` (`b.eq +0x3cc`) to `+0x3cc` (`store_session`). -/
theorem p4_seg3c_ok_ext_wp_p4 {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : StageP4Alloc b A ext)
    (s : State) (coroPtr removePreKeyFutPtr removePreKeyFutVt futSize futAlign : BitVec 64)
    (hsize_nz : futSize ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x298#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = removePreKeyFutPtr)
    (hx23 : s.readReg64 .x23 = removePreKeyFutVt)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3cc#64) s
      (((removePreKeyFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
       ((removePreKeyFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
       A.live removePreKeyFutPtr futSize.toNat futAlign.toNat ∗
       memRegion removePreKeyFutPtr futSize.toNat ∗
       A.pool ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((removePreKeyFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
          ((removePreKeyFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
          A.pool ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  have hdealloc := dealloc_at_closure_p4 hA
  have hsize_beq : (futSize == 0#64) = false := beq_eq_false_iff_ne.mpr hsize_nz
  closure_fetches_range_cli b (Rust.withPanics ext) 0x298 0x2b0
  dsimp only [tripleRatchetProgAtExt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = removePreKeyFutPtr := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = removePreKeyFutVt := hx23
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 0xfffffffffffffffe#64 := hx28
  wp_steps
  wp_call hdealloc (removePreKeyFutPtr, futSize.toNat, futAlign.toNat)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl),
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

theorem p4_seg3c_ok_ext_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContracts b A ext)
    (s : State) (coroPtr removePreKeyFutPtr removePreKeyFutVt futSize futAlign : BitVec 64)
    (hsize_nz : futSize ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x298#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = removePreKeyFutPtr)
    (hx23 : s.readReg64 .x23 = removePreKeyFutVt)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3cc#64) s
      (((removePreKeyFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
       ((removePreKeyFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
       A.live removePreKeyFutPtr futSize.toNat futAlign.toNat ∗
       memRegion removePreKeyFutPtr futSize.toNat ∗
       A.pool ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((removePreKeyFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
          ((removePreKeyFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
          A.pool ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) :=
  p4_seg3c_ok_ext_wp_p4 b ext (.of_allocContracts hA) s coroPtr removePreKeyFutPtr
    removePreKeyFutVt futSize futAlign hsize_nz hpc hrun hsp hx19 hx21 hx23 hx28

/-- `+0x298 → +0x550` (`Err(e)`, `w0 + 2#64 ≠ 0#64`): deallocates `removePreKeyFutPtr`, falls
    through `+0x2b0` (`b.eq +0x3cc` not taken), sets `x8 := s.sp + 0x310#64` at `+0x2b4`, and
    branches at `+0x2b8` (`b +0x550`) to the shared unwind entry `+0x550`. -/
theorem p4_seg3c_err_ext_wp_p4 {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : StageP4Alloc b A ext)
    (s : State) (coroPtr removePreKeyFutPtr removePreKeyFutVt futSize futAlign w0 : BitVec 64)
    (hsize_nz : futSize ≠ 0#64)
    (hw0_ne_ok : w0 + 2#64 ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x298#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = removePreKeyFutPtr)
    (hx23 : s.readReg64 .x23 = removePreKeyFutVt)
    (hx28 : s.readReg64 .x28 = w0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x550#64) s
      (((removePreKeyFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
       ((removePreKeyFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
       A.live removePreKeyFutPtr futSize.toNat futAlign.toNat ∗
       memRegion removePreKeyFutPtr futSize.toNat ∗
       A.pool ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((removePreKeyFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
          ((removePreKeyFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
          A.pool ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x8 = s.sp + 0x310#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = w0 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  have hdealloc := dealloc_at_closure_p4 hA
  have hsize_beq : (futSize == 0#64) = false := beq_eq_false_iff_ne.mpr hsize_nz
  have hw0_beq : (w0 + 2#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hw0_ne_ok
  closure_fetches_range_cli b (Rust.withPanics ext) 0x298 0x2b8
  dsimp only [tripleRatchetProgAtExt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = removePreKeyFutPtr := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = removePreKeyFutVt := hx23
  have hx28' : s.readReg64 (Reg.gpr 28#5) = w0 := hx28
  wp_steps
  wp_call hdealloc (removePreKeyFutPtr, futSize.toNat, futAlign.toNat)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl),
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem p4_seg3c_err_ext_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContracts b A ext)
    (s : State) (coroPtr removePreKeyFutPtr removePreKeyFutVt futSize futAlign w0 : BitVec 64)
    (hsize_nz : futSize ≠ 0#64)
    (hw0_ne_ok : w0 + 2#64 ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x298#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = removePreKeyFutPtr)
    (hx23 : s.readReg64 .x23 = removePreKeyFutVt)
    (hx28 : s.readReg64 .x28 = w0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x550#64) s
      (((removePreKeyFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
       ((removePreKeyFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
       A.live removePreKeyFutPtr futSize.toNat futAlign.toNat ∗
       memRegion removePreKeyFutPtr futSize.toNat ∗
       A.pool ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((removePreKeyFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
          ((removePreKeyFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
          A.pool ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x8 = s.sp + 0x310#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = w0 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) :=
  p4_seg3c_err_ext_wp_p4 b ext (.of_allocContracts hA) s coroPtr removePreKeyFutPtr
    removePreKeyFutVt futSize futAlign w0 hsize_nz hw0_ne_ok hpc hrun hsp hx19 hx21 hx23 hx28

/-! ## Vtable bundle for `remove_pre_key` -/

/-- Read-only `.rodata` vtable bundle for `pkKit`'s `remove_pre_key` future. -/
def removePreKeyVtablesAt {A : RustAlloc} {b : BitVec 64}
    (pkKit : PreKeyStoreSpec A b) : SepProp :=
  ((b + pkKit.removeFutVtOff) ↦₆₄ᵣ (b + pkKit.removeFutDropOff)) ∗
  ((b + pkKit.removeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.removeBoxSize) ∗
  ((b + pkKit.removeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((b + pkKit.removeFutVtOff + 0x18#64) ↦₆₄ᵣ (b + pkKit.removePollOff))

theorem removePreKeyVtablesAt_intro {A : RustAlloc} {img : Obj.Image}
    {pkKit : PreKeyStoreSpec A img.base} (hvt : PreKeyVtablesOk img pkKit)
    {s : State} {P : SepProp} (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ removePreKeyVtablesAt pkKit ∗ P := by
  unfold removePreKeyVtablesAt
  simp only [sepConj_assoc]
  exact hvt.removeFutDrop hF
    (hvt.removeFutSize hF (hvt.removeFutAlign hF (hvt.removeFutPoll hF hP)))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
