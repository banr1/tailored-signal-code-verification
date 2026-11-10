/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Defs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4SaveId
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Stage P4.4 Segments: `SessionStore::store_session` and `Ok(pt)` Exit

Basic-block `SepWP` segments (`+0x3cc → storeShim`, `+0x3e0 → storePoll`, `+0x3f8 → storeFutDrop`,
`+0x444 → dropSessionStructure3` / `+0x550`, `+0x48c → x30`) and vtable / representation helpers
for Substage P4.4 on `tripleRatchetProgAtExt img.base ext`.
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
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
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

/-! ## Basic-block `SepWP` segments for Substage P4.4 -/

/-- `+0x3cc → storeSessionShimAddr`: loads `(sessionStorePtr, sessionStoreVt)` from
    `coroPtr + 0x88..0x90` and `remoteAddrPtr = [coroPtr + 0x78]`, sets `x2 := coroPtr + 0xe0#64`,
    and dispatches `session_store.store_session(remote_addr, &session_record)` via
    `[sessionStoreVt + 0x20]`. -/
theorem p4_seg4a_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State)
    (coroPtr remoteAddrPtr sessionStorePtr sessionStoreVt storeSessionShimAddr : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3cc#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAtExt b ext) storeSessionShimAddr s
      (((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x88#64) ↦₆₄ sessionStorePtr) ∗
       ((coroPtr + 0x90#64) ↦₆₄ sessionStoreVt) ∗
       ((sessionStoreVt + 0x20#64) ↦₆₄ᵣ storeSessionShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
          ((coroPtr + 0x88#64) ↦₆₄ sessionStorePtr) ∗
          ((coroPtr + 0x90#64) ↦₆₄ sessionStoreVt) ∗
          ((sessionStoreVt + 0x20#64) ↦₆₄ᵣ storeSessionShimAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = sessionStorePtr ∧
        s1.readReg64 .x1 = remoteAddrPtr ∧
        s1.readReg64 .x2 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3e0#64) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 0x3cc 0x3dc
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- `+0x3e0 → storeSessionPollAddr`: stores `(storeSessionFutPtr, storeSessionFutVt)` at
    `coroPtr + 0x2c8..0x2d0` and polls `store_session` into `sp + 0x3e0..0x410`. -/
theorem p4_seg4b_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr ctxPtr storeSessionFutPtr storeSessionFutVt storeSessionPollAddr
    u_2c8 u_2d0 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3e0#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = storeSessionFutPtr)
    (hx1 : s.readReg64 .x1 = storeSessionFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr) :
    SepWP (tripleRatchetProgAtExt b ext) storeSessionPollAddr s
      (((coroPtr + 0x2c8#64) ↦₆₄ u_2c8) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ u_2d0) ∗
       ((storeSessionFutVt + 0x18#64) ↦₆₄ᵣ storeSessionPollAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x2c8#64) ↦₆₄ storeSessionFutPtr) ∗
          ((coroPtr + 0x2d0#64) ↦₆₄ storeSessionFutVt) ∗
          ((storeSessionFutVt + 0x18#64) ↦₆₄ᵣ storeSessionPollAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = storeSessionFutPtr ∧
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
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3f8#64) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 0x3e0 0x3f4
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = storeSessionFutPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = storeSessionFutVt := hx1
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx27' : s.readReg64 (Reg.gpr 27#5) = ctxPtr := hx27
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- `+0x3f8 → storeSessionDropAddr` (via `+0x414..+0x440`) for any ready tag `w0`
    (`w0 + 3#64 ≠ 0#64`, covering both `Ok(())` and `Err(())`):
    copies `sp + 0x3ec..0x410` into `sp + 0x340..0x364`, sets `x22 := o1.zeroExtend 64`,
    `x28 := w0`, and calls `drop_in_place` (`[storeSessionFutVt]`) on `storeSessionFutPtr`. -/
theorem p4_seg4c_gen_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr storeSessionFutPtr storeSessionFutVt storeSessionDropAddr w0
    o2 o3 o4 o5 u_340 u_348 u_350 u_358 : BitVec 64)
    (o1 o6 u_360 : BitVec 32)
    (hw0_ne_pend : w0 + 3#64 ≠ 0#64)
    (hdrop_nz : storeSessionDropAddr ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3f8#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) :
    SepWP (tripleRatchetProgAtExt b ext) storeSessionDropAddr s
      (((coroPtr + 0x2c8#64) ↦₆₄ storeSessionFutPtr) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ storeSessionFutVt) ∗
       (storeSessionFutVt ↦₆₄ᵣ storeSessionDropAddr) ∗
       stagingCellsAt (s.sp + 0x340#64) u_340 u_348 u_350 u_358 u_360 ∗
       pollCellsAt (s.sp + 0x3e0#64) w0 o1 o2 o3 o4 o5 o6)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x2c8#64) ↦₆₄ storeSessionFutPtr) ∗
          ((coroPtr + 0x2d0#64) ↦₆₄ storeSessionFutVt) ∗
          (storeSessionFutVt ↦₆₄ᵣ storeSessionDropAddr) ∗
          stagingCellsAt (s.sp + 0x340#64) o2 o3 o4 o5 o6 ∗
          pollCellsAt (s.sp + 0x3e0#64) w0 o1 o2 o3 o4 o5 o6) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = storeSessionFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = storeSessionFutPtr ∧
        s1.readReg64 .x22 = o1.zeroExtend 64 ∧
        s1.readReg64 .x23 = storeSessionFutVt ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = w0 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x444#64) := by
  have hw0_beq : (w0 + 3#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hw0_ne_pend
  have hdrop_beq : (storeSessionDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  unfold stagingCellsAt pollCellsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  closure_fetches_range_cli b (Rust.withPanics ext) 0x3f8 0x400
  closure_fetches_range_cli b (Rust.withPanics ext) 0x414 0x440
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

/-- `+0x444 → dropSessionStructure3Name` (`Ok(())`, `x28 = -2`): deallocates
    `storeSessionFutPtr`, copies the 24-byte `ptext` `Vec<u8>` from `coroPtr + 0x280..0x298` into
    `W22` + `sp + 0x370..0x384`, checks `[coroPtr + 0xf8] ≠ -1`, and calls
    `drop_glue::<SessionStructure> [local#4]` on `coroPtr + 0xf8` with `x30 = +0x48c`. -/
theorem p4_seg4d_ok_ext_wp_p4 {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : StageP4Alloc b A ext)
    (s : State) (coroPtr storeSessionFutPtr storeSessionFutVt futSize futAlign
    curStateWord0 ptextMid0 ptextMid1 u_370 u_378 : BitVec 64)
    (ptextHead ptextTail u_380 : BitVec 32)
    (hsize_nz : futSize ≠ 0#64)
    (hcur_ne : curStateWord0 + 1#64 ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x444#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = storeSessionFutPtr)
    (hx23 : s.readReg64 .x23 = storeSessionFutVt)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name) s
      (((coroPtr + 0xf8#64) ↦₆₄ curStateWord0) ∗
       ((coroPtr + 0x280#64) ↦₃₂ ptextHead) ∗
       ((coroPtr + 0x284#64) ↦₆₄ ptextMid0) ∗
       ((coroPtr + 0x28c#64) ↦₆₄ ptextMid1) ∗
       ((coroPtr + 0x294#64) ↦₃₂ ptextTail) ∗
       ((storeSessionFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
       ((storeSessionFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
       ((s.sp + 0x370#64) ↦₆₄ u_370) ∗
       ((s.sp + 0x378#64) ↦₆₄ u_378) ∗
       ((s.sp + 0x380#64) ↦₃₂ u_380) ∗
       A.live storeSessionFutPtr futSize.toNat futAlign.toNat ∗
       memRegion storeSessionFutPtr futSize.toNat ∗
       A.pool ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xf8#64) ↦₆₄ curStateWord0) ∗
          ((coroPtr + 0x280#64) ↦₃₂ ptextHead) ∗
          ((coroPtr + 0x284#64) ↦₆₄ ptextMid0) ∗
          ((coroPtr + 0x28c#64) ↦₆₄ ptextMid1) ∗
          ((coroPtr + 0x294#64) ↦₃₂ ptextTail) ∗
          ((storeSessionFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
          ((storeSessionFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
          ((s.sp + 0x370#64) ↦₆₄ ptextMid0) ∗
          ((s.sp + 0x378#64) ↦₆₄ ptextMid1) ∗
          ((s.sp + 0x380#64) ↦₃₂ ptextTail) ∗
          A.pool ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = ptextHead.zeroExtend 64 ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x48c#64) := by
  have hdealloc := dealloc_at_closure_p4 hA
  have hsize_beq : (futSize == 0#64) = false := beq_eq_false_iff_ne.mpr hsize_nz
  have hcur_beq : (curStateWord0 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hcur_ne
  closure_fetches_range_cli b (Rust.withPanics ext) 0x444 0x488
  dsimp only [tripleRatchetProgAtExt] at hdealloc hpc ⊢
  have htarget :
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        bv% ((2^64 +
          ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64) =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
        (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"),
        (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")]
    bv_omega
  rw [← htarget]
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = storeSessionFutPtr := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = storeSessionFutVt := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 0xfffffffffffffffe#64 := hx28
  wp_steps
  wp_call hdealloc (storeSessionFutPtr, futSize.toNat, futAlign.toNat)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl),
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

theorem p4_seg4d_ok_ext_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContracts b A ext)
    (s : State) (coroPtr storeSessionFutPtr storeSessionFutVt futSize futAlign
    curStateWord0 ptextMid0 ptextMid1 u_370 u_378 : BitVec 64)
    (ptextHead ptextTail u_380 : BitVec 32)
    (hsize_nz : futSize ≠ 0#64)
    (hcur_ne : curStateWord0 + 1#64 ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x444#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = storeSessionFutPtr)
    (hx23 : s.readReg64 .x23 = storeSessionFutVt)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name) s
      (((coroPtr + 0xf8#64) ↦₆₄ curStateWord0) ∗
       ((coroPtr + 0x280#64) ↦₃₂ ptextHead) ∗
       ((coroPtr + 0x284#64) ↦₆₄ ptextMid0) ∗
       ((coroPtr + 0x28c#64) ↦₆₄ ptextMid1) ∗
       ((coroPtr + 0x294#64) ↦₃₂ ptextTail) ∗
       ((storeSessionFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
       ((storeSessionFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
       ((s.sp + 0x370#64) ↦₆₄ u_370) ∗
       ((s.sp + 0x378#64) ↦₆₄ u_378) ∗
       ((s.sp + 0x380#64) ↦₃₂ u_380) ∗
       A.live storeSessionFutPtr futSize.toNat futAlign.toNat ∗
       memRegion storeSessionFutPtr futSize.toNat ∗
       A.pool ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xf8#64) ↦₆₄ curStateWord0) ∗
          ((coroPtr + 0x280#64) ↦₃₂ ptextHead) ∗
          ((coroPtr + 0x284#64) ↦₆₄ ptextMid0) ∗
          ((coroPtr + 0x28c#64) ↦₆₄ ptextMid1) ∗
          ((coroPtr + 0x294#64) ↦₃₂ ptextTail) ∗
          ((storeSessionFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
          ((storeSessionFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
          ((s.sp + 0x370#64) ↦₆₄ ptextMid0) ∗
          ((s.sp + 0x378#64) ↦₆₄ ptextMid1) ∗
          ((s.sp + 0x380#64) ↦₃₂ ptextTail) ∗
          A.pool ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = ptextHead.zeroExtend 64 ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x48c#64) :=
  p4_seg4d_ok_ext_wp_p4 b ext (.of_allocContracts hA) s coroPtr storeSessionFutPtr
    storeSessionFutVt futSize futAlign curStateWord0 ptextMid0 ptextMid1 u_370 u_378
    ptextHead ptextTail u_380 hsize_nz hcur_ne hpc hrun hsp hx19 hx21 hx23 hx24 hx28

/-- `+0x444 → +0x550` (`Err(())`, `w0 + 2#64 ≠ 0#64`): deallocates `storeSessionFutPtr`,
    branches at `+0x45c` (`b.ne +0x4fc`) to `+0x4fc`, sets `x8 := s.sp + 0x340#64`, and branches
    at `+0x500` (`b +0x550`) to the shared unwind entry `+0x550`. -/
theorem p4_seg4d_err_ext_wp_p4 {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : StageP4Alloc b A ext)
    (s : State) (coroPtr storeSessionFutPtr storeSessionFutVt futSize futAlign w0 : BitVec 64)
    (hsize_nz : futSize ≠ 0#64)
    (hw0_ne_ok : w0 + 2#64 ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x444#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = storeSessionFutPtr)
    (hx23 : s.readReg64 .x23 = storeSessionFutVt)
    (hx28 : s.readReg64 .x28 = w0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x550#64) s
      (((storeSessionFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
       ((storeSessionFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
       A.live storeSessionFutPtr futSize.toNat futAlign.toNat ∗
       memRegion storeSessionFutPtr futSize.toNat ∗
       A.pool ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((storeSessionFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
          ((storeSessionFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
          A.pool ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x8 = s.sp + 0x340#64 ∧
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
  closure_fetches_range_cli b (Rust.withPanics ext) 0x444 0x45c
  closure_fetches_range_cli b (Rust.withPanics ext) 0x4fc 0x500
  dsimp only [tripleRatchetProgAtExt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = storeSessionFutPtr := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = storeSessionFutVt := hx23
  have hx28' : s.readReg64 (Reg.gpr 28#5) = w0 := hx28
  wp_steps
  wp_call hdealloc (storeSessionFutPtr, futSize.toNat, futAlign.toNat)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl),
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem p4_seg4d_err_ext_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContracts b A ext)
    (s : State) (coroPtr storeSessionFutPtr storeSessionFutVt futSize futAlign w0 : BitVec 64)
    (hsize_nz : futSize ≠ 0#64)
    (hw0_ne_ok : w0 + 2#64 ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x444#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = storeSessionFutPtr)
    (hx23 : s.readReg64 .x23 = storeSessionFutVt)
    (hx28 : s.readReg64 .x28 = w0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x550#64) s
      (((storeSessionFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
       ((storeSessionFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
       A.live storeSessionFutPtr futSize.toNat futAlign.toNat ∗
       memRegion storeSessionFutPtr futSize.toNat ∗
       A.pool ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((storeSessionFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
          ((storeSessionFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
          A.pool ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x8 = s.sp + 0x340#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = w0 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) :=
  p4_seg4d_err_ext_wp_p4 b ext (.of_allocContracts hA) s coroPtr storeSessionFutPtr
    storeSessionFutVt futSize futAlign w0 hsize_nz hw0_ne_ok hpc hrun hsp hx19 hx21 hx23 hx28
/-- `+0x48c → retAddr` (via `+0x504..+0x508`, `+0x7d0..+0x7d4`, `+0x35ec..+0x362c`):
    checks empty `previous_states` (`coroPtr + 0xe0..0xf8`), sets `x28 = -2`, writes
    `Poll::Ready(Ok(ptext))` to `outPtr + 0x0..0x30`, marks `[coroPtr + 0x2c0] ↦₈ 1#8`,
    restores `X19..X30` and `SP = s.sp + 0xcd0#64`, and returns to `retAddr`. -/
theorem p4_seg4e_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr outPtr prevStatesPtr
    ptextMid0 ptextMid1 w_380 w_388
    u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
    savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (ptextHead w_390 u_ret08 u_ret2c : BitVec 32)
    (b_2c0 : BitVec 8)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x48c#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = ptextHead.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr) :
    SepWP (tripleRatchetProgAtExt b ext) retAddr s
      (((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((outPtr + 0x0#64) ↦₆₄ u_ret0) ∗
       ((outPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((outPtr + 0xc#64) ↦₆₄ u_ret0c) ∗
       ((outPtr + 0x14#64) ↦₆₄ u_ret14) ∗
       ((outPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗
       ((outPtr + 0x24#64) ↦₆₄ u_ret24) ∗
       ((outPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗
       ((s.sp + 0x370#64) ↦₆₄ ptextMid0) ∗
       ((s.sp + 0x378#64) ↦₆₄ ptextMid1) ∗
       ((s.sp + 0x380#64) ↦₆₄ w_380) ∗
       ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗
       ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗
       ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗
       ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗
       ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗
       ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗
       ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((outPtr + 0x0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((outPtr + 0x8#64) ↦₃₂ ptextHead) ∗
          ((outPtr + 0xc#64) ↦₆₄ ptextMid0) ∗
          ((outPtr + 0x14#64) ↦₆₄ ptextMid1) ∗
          ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗
          ((outPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ ptextMid0) ∗
          ((s.sp + 0x378#64) ↦₆₄ ptextMid1) ∗
          ((s.sp + 0x380#64) ↦₆₄ w_380) ∗
          ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
          ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
          ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗
          ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
          ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗
          ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗
          ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
          ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗
          ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗
          ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗
          ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = savedX19 ∧
        s1.readReg64 .x20 = savedX20 ∧
        s1.readReg64 .x21 = savedX21 ∧
        s1.readReg64 .x22 = savedX22 ∧
        s1.readReg64 .x23 = savedX23 ∧
        s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧
        s1.readReg64 .x26 = savedX26 ∧
        s1.readReg64 .x27 = savedX27 ∧
        s1.readReg64 .x28 = savedX28 ∧
        s1.readReg64 .x29 = savedX29 ∧
        s1.readReg64 .x30 = retAddr) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 0x48c 0x490
  closure_fetches_range_cli b (Rust.withPanics ext) 0x504 0x508
  closure_fetches_range_cli b (Rust.withPanics ext) 0x7d0 0x7d4
  closure_fetches_range_cli b (Rust.withPanics ext) 0x35ec 0x362c
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = ptextHead.zeroExtend 64 := hx22
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl),
    by simp_all [arm64_norm], rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-! ## Vtable and session-representation helpers -/

/-- Read-only vtable cells required by Substage P4.4 (`store_session`). -/
def storeSessionVtablesAt {A : RustAlloc} (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) : SepProp :=
  ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (img.base + kit.storeShimOff)) ∗
  ((img.base + kit.storeFutVtOff) ↦₆₄ᵣ (img.base + kit.storeFutDropOff)) ∗
  ((img.base + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
  ((img.base + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((img.base + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.storePollOff))

theorem storeSessionVtablesAt_intro {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {s : State} {P : SepProp}
    (hvt : SessionOnlyVtablesOk img kit)
    (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ storeSessionVtablesAt img kit ∗ P := by
  unfold storeSessionVtablesAt
  simp only [sepConj_assoc]
  exact hvt.storeSlot hF
    (hvt.storeFutDrop hF
      (hvt.storeFutSize hF
        (hvt.storeFutAlign hF
          (hvt.storeFutPoll hF hP))))

theorem stack_storeSession_to_alloc {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (sp : BitVec 64)
    (hn : storeSessionCallStack kit ≤ 2 ^ 64) :
    stackAt sp (storeSessionCallStack kit) =
      memRegion (sp - BitVec.ofNat 64 (storeSessionCallStack kit))
        (storeSessionCallStack kit - allocHookStack) ∗
        stackAt sp allocHookStack :=
  stackAt_sub_eq sp (storeSessionCallStack kit) allocHookStack
    (Nat.le_trans allocHookStack_le_errUnwind
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))) hn

theorem stack_storeSession_to_dropSS3 {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (sp : BitVec 64)
    (hn : storeSessionCallStack kit ≤ 2 ^ 64) :
    stackAt sp (storeSessionCallStack kit) =
      memRegion (sp - BitVec.ofNat 64 (storeSessionCallStack kit))
        (storeSessionCallStack kit - dropSessionStructureLocal2Stack) ∗
        stackAt sp dropSessionStructureLocal2Stack :=
  stackAt_sub_eq sp (storeSessionCallStack kit) dropSessionStructureLocal2Stack
    (Nat.le_trans dropSS3Stack_le_errUnwind
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))) hn

/-- Unpack `storePollOutAt b p (.ok ())` into `pollCellsAt p (-2) ...`. -/
theorem storePollOk_eq_exists_pollCells (b p : BitVec 64) :
    storePollOutAt b p (.ok ()) =
      ∃∗ o1 : BitVec 32, ∃∗ o6 : BitVec 32, ∃∗ o5 : BitVec 64,
      ∃∗ o4 : BitVec 64, ∃∗ o3 : BitVec 64, ∃∗ o2 : BitVec 64,
        pollCellsAt p 0xfffffffffffffffe#64 o1 o2 o3 o4 o5 o6 := by
  dsimp only [storePollOutAt]
  rw [ProofLib.memRegion_split' (b := p + 8#64) (n := 4) (k := 36)
        (b' := p + 0xc#64) rfl (by bv_omega) (by decide),
      ← sepConj_assoc,
      ProofLib.memRegion_four (p + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine congrArg sepExists (funext fun o1 => ?_)
  rw [memRegion36_eq_exists_stagingCells (p + 0xc#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine congrArg sepExists (funext fun o6 =>
    congrArg sepExists (funext fun o5 =>
    congrArg sepExists (funext fun o4 =>
    congrArg sepExists (funext fun o3 =>
    congrArg sepExists (funext fun o2 => ?_)))))
  unfold stagingCellsAt pollCellsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

/-- Layout-independent unpack + repack of `storePollOutAt b p (.error ())` into `pollCellsAt`. -/
theorem storePollErr_unpack_repack (b p : BitVec 64) :
    storePollOutAt b p (.error ()) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ o1 : BitVec 32, ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64,
      ∃∗ o4 : BitVec 64, ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32, ∃∗ H_err : SepProp,
        ⌜w0 = 0x800000000000001A#64 ∧
          (∀ outPtr : BitVec 64,
            pollCellsAt outPtr w0 o1 o2 o3 o4 o5 o6 ∗ H_err ⊢
              storePollOutAt b outPtr (.error ()))⌝ ∗
        pollCellsAt p w0 o1 o2 o3 o4 o5 o6 ∗ H_err := by
  dsimp only [storePollOutAt]
  exact fiveWords_tail_unpack_repack p _ _ _ _ _ _ rfl

/-- Pure `Session` extra-field relation complementing `sessionStateAt` inside
`sessionStateReprAt`. -/
def SessionExtraRel (G : SessionGhost) (ss : Session (List (BitVec 8))) : Prop :=
  PendingRel G.pending ss.pendingPreKey ∧
  KyberRel G.kyber ss.pendingKyberPreKey ∧
  G.alice.bytes = ss.aliceBaseKey ∧
  G.regIds.take 4 = leBytes 4 ss.remoteRegistrationId.toNat ∧
  (G.regIds.drop 4).take 4 = leBytes 4 ss.localRegistrationId.toNat

/-- Fold `sessionStateAt` + empty `previous_states` header into `sessionRecordAt` (`Some ss`). -/
theorem p4_sessionRecordAt_some_prev_of_state (A : RustAlloc) (r prevPtr : BitVec 64)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hprev_nz : prevPtr ≠ 0#64) (hExtra : SessionExtraRel G ss) :
    (r ↦₆₄ 0#64) ∗ ((r + 0x8#64) ↦₆₄ prevPtr) ∗ ((r + 0x10#64) ↦₆₄ 0#64) ∗
    sessionStateAt A (r + 0x18#64) G ss.state ⊢
    sessionRecordAt A r ⟨0#64, prevPtr, some G⟩ ⟨some ss⟩ := by
  unfold sessionRecordAt vecAt vecHeader vecBuf sessionStateReprAt
  have h10 : r + 16#64 = r + 0x10#64 := rfl
  have h8 : r + 8#64 = r + 0x8#64 := rfl
  have h0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [h10, h8, h0, ↓reduceIte, sepConj_emp, emp_sepConj, List.length_nil, sepConj_assoc]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  refine Entails.pure_right ⟨Nat.zero_le _, by decide, hprev_nz⟩ ?_
  exact Entails.pure_right hExtra (Entails.refl _)

/-- Unfold `sessionRecordAt` (`Some ss`) back into empty `previous_states` header + `sessionStateAt`. -/
theorem p4_sessionRecordAt_some_prev_to_state (A : RustAlloc) (r prevPtr : BitVec 64)
    (G : SessionGhost) (ss : Session (List (BitVec 8))) :
    sessionRecordAt A r ⟨0#64, prevPtr, some G⟩ ⟨some ss⟩ ⊢
    (r ↦₆₄ 0#64) ∗ ((r + 0x8#64) ↦₆₄ prevPtr) ∗ ((r + 0x10#64) ↦₆₄ 0#64) ∗
    sessionStateAt A (r + 0x18#64) G ss.state := by
  unfold sessionRecordAt vecAt vecHeader vecBuf sessionStateReprAt
  have h10 : r + 16#64 = r + 0x10#64 := rfl
  have h8 : r + 8#64 = r + 0x8#64 := rfl
  have h0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [h10, h8, h0, ↓reduceIte, sepConj_emp, emp_sepConj, List.length_nil, sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (Entails.pure_left fun _ => Entails.pure_left fun _ => Entails.refl _)))

theorem sp370_36_split_eq' (sp : BitVec 64) :
    memRegion (sp + 0x370#64) 36 =
      ∃∗ w_390 : BitVec 32, ∃∗ w_388 : BitVec 64, ∃∗ u_384 : BitVec 32,
      ∃∗ u_380 : BitVec 32, ∃∗ u_378 : BitVec 64, ∃∗ u_370 : BitVec 64,
        ((sp + 0x370#64) ↦₆₄ u_370) ∗
        ((sp + 0x378#64) ↦₆₄ u_378) ∗
        ((sp + 0x380#64) ↦₃₂ u_380) ∗
        ((sp + 0x384#64) ↦₃₂ u_384) ∗
        ((sp + 0x388#64) ↦₆₄ w_388) ∗
        ((sp + 0x390#64) ↦₃₂ w_390) := by
  rw [ProofLib.memRegion_split' (b := sp + 0x370#64) (n := 8) (k := 28)
        (b' := sp + 0x378#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x378#64) (n := 8) (k := 20)
        (b' := sp + 0x380#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x380#64) (n := 4) (k := 16)
        (b' := sp + 0x384#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x384#64) (n := 4) (k := 12)
        (b' := sp + 0x388#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x388#64) (n := 8) (k := 4)
        (b' := sp + 0x390#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 0x370#64),
      ProofLib.memRegion_eight (sp + 0x378#64),
      ProofLib.memRegion_four (sp + 0x380#64),
      ProofLib.memRegion_four (sp + 0x384#64),
      ProofLib.memRegion_eight (sp + 0x388#64),
      ProofLib.memRegion_four (sp + 0x390#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem pointsTo32_pair_sp380' (sp : BitVec 64) (lo hi : BitVec 32) :
    (((sp + 0x380#64) ↦₃₂ lo) ∗ ((sp + 0x384#64) ↦₃₂ hi)) =
      ((sp + 0x380#64) ↦₆₄ (hi ++ lo)) := by
  have h : sp + 0x384#64 = (sp + 0x380#64) + 4#64 := by bv_omega
  rw [h, pointsTo32_pair_eq]

theorem pointsTo32_pair_out1c' (outPtr : BitVec 64) (lo hi : BitVec 32) :
    ((outPtr + 0x1c#64) ↦₆₄ (hi ++ lo)) =
      (((outPtr + 0x1c#64) ↦₃₂ lo) ∗ ((outPtr + 0x20#64) ↦₃₂ hi)) := by
  have h : outPtr + 0x20#64 = (outPtr + 0x1c#64) + 4#64 := by bv_omega
  rw [h, ← pointsTo32_pair_eq]

theorem memRegion16_out20_fold' (outPtr w_24 : BitVec 64) (u_20 w_2c : BitVec 32) :
    ((outPtr + 0x20#64) ↦₃₂ u_20) ∗
    ((outPtr + 0x24#64) ↦₆₄ w_24) ∗
    ((outPtr + 0x2c#64) ↦₃₂ w_2c) ⊢ memRegion (outPtr + 0x20#64) 16 := by
  rw [ProofLib.memRegion_split' (b := outPtr + 0x20#64) (n := 4) (k := 12)
        (b' := outPtr + 0x24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outPtr + 0x24#64) (n := 8) (k := 4)
        (b' := outPtr + 0x2c#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo32_entails_memRegion _ _))

/-- Fold the closure's `Ok(ptext)` sret cells and heap buffer into `vecResultAt A outPtr (.ok pt)`. -/
theorem p4_fold_decResultAt_ok (A : RustAlloc) (outPtr ptCap ptPtr : BitVec 64)
    (pt : List (BitVec 8))
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64) :
    (outPtr ↦₆₄ 0xfffffffffffffffe#64) ∗
    ((outPtr + 0x8#64) ↦₃₂ ptCap.extractLsb' 0 32) ∗
    ((outPtr + 0xc#64) ↦₆₄ (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)) ∗
    ((outPtr + 0x14#64) ↦₆₄
      ((BitVec.ofNat 64 pt.length).extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)) ∗
    ((outPtr + 0x1c#64) ↦₃₂ (BitVec.ofNat 64 pt.length).extractLsb' 32 32) ∗
    (ptPtr ↦ₛ pt) ∗
    (if ptCap = 0#64 then emp
     else A.live ptPtr ptCap.toNat 1 ∗
       memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
    memRegion (outPtr + 0x20#64) 16 ⊢
    vecResultAt A outPtr (.ok pt) := by
  have hhdr :
      ((outPtr + 0x8#64) ↦₃₂ ptCap.extractLsb' 0 32) ∗
      ((outPtr + 0xc#64) ↦₆₄ (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)) ∗
      ((outPtr + 0x14#64) ↦₆₄
        ((BitVec.ofNat 64 pt.length).extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)) ∗
      ((outPtr + 0x1c#64) ↦₃₂ (BitVec.ofNat 64 pt.length).extractLsb' 32 32) =
      vecHeader (outPtr + 0x8#64) ptCap ptPtr (BitVec.ofNat 64 pt.length) := by
    unfold vecHeader
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (words3_eq_head_mid_tail (outPtr + 0x8#64) ptCap ptPtr (BitVec.ofNat 64 pt.length)).symm
  have hbuf :
      (ptPtr ↦ₛ pt) ∗
      (if ptCap = 0#64 then emp
       else A.live ptPtr ptCap.toNat 1 ∗
         memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) =
      (if ptCap = 0 then emp
       else A.live ptPtr ptCap.toNat 1 ∗ (ptPtr ↦ₛ pt) ∗
         memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) := by
    by_cases hcap : ptCap = 0#64
    · subst hcap
      have hnil : pt = [] := List.eq_nil_of_length_eq_zero (by simpa using hpt_le)
      subst hnil
      simp [pointsToBytes_nil, emp_sepConj]
    · have hcap0 : ptCap ≠ 0 := hcap
      simp only [hcap, hcap0, ↓reduceIte]
      ac_rfl
  dsimp only [vecResultAt]
  change _ ⊢ (outPtr ↦₆₄ 0xfffffffffffffffe#64) ∗ vecU8 A (outPtr + 0x8#64) pt ∗
    memRegion (outPtr + 0x20#64) 16
  have heq :
      (outPtr ↦₆₄ 0xfffffffffffffffe#64) ∗
      ((outPtr + 0x8#64) ↦₃₂ ptCap.extractLsb' 0 32) ∗
      ((outPtr + 0xc#64) ↦₆₄ (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)) ∗
      ((outPtr + 0x14#64) ↦₆₄
        ((BitVec.ofNat 64 pt.length).extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)) ∗
      ((outPtr + 0x1c#64) ↦₃₂ (BitVec.ofNat 64 pt.length).extractLsb' 32 32) ∗
      (ptPtr ↦ₛ pt) ∗
      (if ptCap = 0#64 then emp
       else A.live ptPtr ptCap.toNat 1 ∗
         memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
      memRegion (outPtr + 0x20#64) 16 =
      (outPtr ↦₆₄ 0xfffffffffffffffe#64) ∗
      vecHeader (outPtr + 0x8#64) ptCap ptPtr (BitVec.ofNat 64 pt.length) ∗
      (if ptCap = 0 then emp
       else A.live ptPtr ptCap.toNat 1 ∗ (ptPtr ↦ₛ pt) ∗
         memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
      memRegion (outPtr + 0x20#64) 16 := calc
    _ = (outPtr ↦₆₄ 0xfffffffffffffffe#64) ∗
        (((outPtr + 0x8#64) ↦₃₂ ptCap.extractLsb' 0 32) ∗
         ((outPtr + 0xc#64) ↦₆₄ (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)) ∗
         ((outPtr + 0x14#64) ↦₆₄
           ((BitVec.ofNat 64 pt.length).extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)) ∗
         ((outPtr + 0x1c#64) ↦₃₂ (BitVec.ofNat 64 pt.length).extractLsb' 32 32)) ∗
        ((ptPtr ↦ₛ pt) ∗
         (if ptCap = 0#64 then emp
          else A.live ptPtr ptCap.toNat 1 ∗
            memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length))) ∗
        memRegion (outPtr + 0x20#64) 16 := by ac_rfl
    _ = (outPtr ↦₆₄ 0xfffffffffffffffe#64) ∗
        vecHeader (outPtr + 0x8#64) ptCap ptPtr (BitVec.ofNat 64 pt.length) ∗
        (if ptCap = 0 then emp
         else A.live ptPtr ptCap.toNat 1 ∗ (ptPtr ↦ₛ pt) ∗
           memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
        memRegion (outPtr + 0x20#64) 16 := by rw [hhdr, hbuf]
  refine Entails.trans (Entails.of_eq heq) ?_
  refine sepConj_mono_right ?_
  rw [← sepConj_assoc]
  refine sepConj_mono_left ?_
  unfold vecU8 vecU8At
  refine Entails.sepExists_right ptCap (Entails.sepExists_right ptPtr ?_)
  exact sepConj_mono_right (Entails.pure_right ⟨hpt_le, hcap_lt, hptr_nz⟩ (Entails.refl _))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
